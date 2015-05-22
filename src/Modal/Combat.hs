{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module Modal.Combat where
import Prelude hiding (mapM, sequence, foldr)
import Control.Applicative
import Control.Monad.Except hiding (mapM, mapM_, sequence)
import Control.Monad.Identity hiding (mapM, mapM_, sequence)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Maybe
import Data.Map (Map)
import Data.Text (Text)
import Data.Traversable
import Modal.Code
import Modal.Def
import Modal.Competition
import Modal.Display
import Modal.Environment (EnvError(UnknownPlayer), Env, insert, nobody)
import Modal.Formulas
import Modal.Parser (Parsable, parser)
import Modal.Statement hiding (Statement(..))
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Text
import Text.Printf (printf)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Modal.Parser as P
import qualified Modal.Statement as S

data DefType = BotT | AgentT | UniverseT deriving (Eq, Ord, Enum)

instance Show DefType where
  show BotT = "bot"
  show AgentT = "agent"
  show UniverseT = "universe"

type SettingErrorM m = (MonadError SettingError m, Applicative m)

data SettingError
  = WrapE EnvError
  | WrapC CompileError
  | UnknownDef DefType Name
  | UnknownEnv DefType Name
  | UnknownEnvCall DefType Name Name
  | EnvCallCollision DefType Name Name
  | DefNameCollision DefType Name
  | EnvNameCollision DefType Name
  | ListMismatch ValType Name [String] [String]
  deriving Eq

instance Show SettingError where
  show (WrapE e) = show e
  show (WrapC e) = show e
  show (UnknownDef t n) = printf "Unknown %s definition: %s" (show t) n
  show (UnknownEnv t n) = printf "Unknown %s environment: %s" (show t) n
  show (UnknownEnvCall t e n) = printf "Unknown call in %s environment %s: %s" (show t) e n
  show (EnvCallCollision t e n) = printf "Name collision in %s environment %s: %s" (show t) e n
  show (DefNameCollision t n) = printf "Name collision for %s %s" (show t) n
  show (EnvNameCollision t n) = printf "Name collision for %s environment %s" (show t) n
  show (ListMismatch t n xs ys) = printf "%s mismatch for %s: %s/%s"
    (show t) n
    (renderArgs id xs)
    (renderArgs id ys)

newtype A = A String deriving (Eq, Ord)
instance Show A where show (A a) = '@' : a
instance Parsable A where parser = A <$> P.anyname
instance Read A where
  readsPrec _ str = [(A x, rest) | not $ null x] where
    (x, rest) = span P.isNameChar str

newtype U = U String deriving (Eq, Ord)
instance Show U where show (U u) = '$' : u
instance Parsable U where parser = U <$> P.anyname
instance Read U where
  readsPrec _ str = [(U x, rest) | not $ null x] where
    (x, rest) = span P.isNameChar str

data BiVar m t = Me m | Them t | ThemVs Name t deriving (Eq, Ord)
instance (Show a, Show o) => Show (BiVar a o) where
  show (Me m) = printf "Me(Them)%s" (show m)
  show (Them t) = printf "Them(Me)%s" (show t)
  show (ThemVs n t) = printf "Them(%s)%s" n (show t)
instance Bifunctor BiVar where
  bimap f g = runIdentity . bitraverse (Identity . f) (Identity . g)
instance Bifoldable BiVar where
  bifoldMap f _ (Me m) = f m
  bifoldMap _ g (Them t) = g t
  bifoldMap _ g (ThemVs _ t) = g t
instance Bitraversable BiVar where
  bitraverse f _ (Me m) = Me <$> f m
  bitraverse _ g (Them t) = Them <$> g t
  bitraverse _ g (ThemVs x t) = ThemVs x <$> g t
instance AgentVar BiVar where
  makeAgentVarParser m t = try mvt <|> try tvm <|> try tvo <?> "a variable" where
    vsEither a b x y z = try (vs a b z) <|> vs x y z
    mvt = Me . snd <$> vsEither (string "A") (nilOr "U") (string "Me") (nilOr "Them") m
    tvm = Them . snd <$> vsEither (string "U") (nilOr "A") (string "Them") (nilOr "Me") t
    tvo = uncurry ThemVs <$> vsEither (string "U") P.anyname (string "Them") P.anyname t
    vs x y z = (,) <$> (x *> P.parens y) <*> z
    nilOr = option () . void . string
instance (Parsable m, Parsable t) => Parsable (BiVar m t) where
  parser = makeAgentVarParser parser parser
instance (Parsable u, Parsable a) => Read (BiVar u a) where
  readsPrec _ s = case parse (parser <* eof) "reading BiVar" (Text.pack s) of
    Right result -> [(result,"")]
    Left err -> error $ show err
instance Canonicalizable2 BiVar where
  canonicalize2 v1 v2 = fmap expandName where
    expandName (Me val) = v1 val
    expandName (Them val) = v2 Nothing val
    expandName (ThemVs other val) = v2 (Just other) val
instance IsMultiVarA BiVar where
  promoteA names i (Me x) = PlayerNPlays names i x
  promoteA names _ (Them x) = UniversePlays names x
  promoteA names i (ThemVs other x) = UniversePlays (alter names i $ const other) x

data MultiVar u a = UPlays u | APlays Name a | APlaysVs Name Name a deriving (Eq, Ord)
instance (Show a, Show o) => Show (MultiVar a o) where
  show (UPlays u) = printf "U(...)%s" (show u)
  show (APlays n a) = printf "%s(U)%s" n (show a)
  show (APlaysVs n other a) = printf "%s(%s)%s" n other (show a)
instance Bifunctor MultiVar where
  bimap f g = runIdentity . bitraverse (Identity . f) (Identity . g)
instance Bifoldable MultiVar where
  bifoldMap f _ (UPlays u) = f u
  bifoldMap _ g (APlays _ a) = g a
  bifoldMap _ g (APlaysVs _ _ a) = g a
instance Bitraversable MultiVar where
  bitraverse f _ (UPlays u) = UPlays <$> f u
  bitraverse _ g (APlays n a) = APlays n <$> g a
  bitraverse _ g (APlaysVs n other a) = APlaysVs n other <$> g a
instance AgentVar MultiVar where
  makeAgentVarParser u a = try uvp <|> try pvu <|> try pvo <?> "a variable" where
    uvp = (\(_, _, x) -> UPlays x)  <$> vs (string "U") (pure ()) u
    pvu = (\(n, _, x) -> APlays n x) <$> vs P.anyname (option () $ void $ string "U") a
    pvo = (\(n, o, x) -> APlaysVs n o x) <$> vs P.anyname P.anyname a
    vs x y z = (,,) <$> x <*> P.parens y <*> z
instance (Parsable u, Parsable a) => Parsable (MultiVar u a) where
  parser = makeAgentVarParser parser parser
instance (Parsable u, Parsable a) => Read (MultiVar u a) where
  readsPrec _ s = case parse (parser <* eof) "reading MultiVar" (Text.pack s) of
    Right result -> [(result,"")]
    Left err -> error $ show err
instance Canonicalizable2 MultiVar where
  canonicalize2 v1 v2 = fmap expandName where
    expandName (UPlays val) = v1 val
    expandName (APlays _ val) = v2 Nothing val
    expandName (APlaysVs _ other val) = v2 (Just other) val
instance IsMultiVarU MultiVar where
  promoteU names (UPlays x) = return $ UniversePlays names x
  promoteU names (APlays n x) =
    maybe (throwError $ UnknownPlayer n) make (List.elemIndex n names)
    where make i = return $ PlayerNPlays names i x
  promoteU names (APlaysVs n other x) =
    maybe (throwError $ UnknownPlayer n) make (List.elemIndex n names)
    where make i = return $ PlayerNPlays (alter names 0 $ const other) i x

newtype AAStatement = AAStatement { getAAStatement :: ModalizedStatement BiVar A A }
  deriving Show
instance IsStatement AAStatement where
  type Var AAStatement = BiVar
  type Act AAStatement = A
  type Out AAStatement = A
  makeStatementParser = fmap AAStatement . modalizedStatementParser
  evalStatement = evalModalizedStatement . getAAStatement

newtype AUStatement = AUStatement { getAUStatement :: ModalizedStatement BiVar A U }
  deriving Show
instance IsStatement AUStatement where
  type Var AUStatement = BiVar
  type Act AUStatement = A
  type Out AUStatement = U
  makeStatementParser = fmap AUStatement . modalizedStatementParser
  evalStatement = evalModalizedStatement . getAUStatement

newtype UStatement = UStatement { getUStatement :: UnrestrictedStatement MultiVar U A }
  deriving Show
instance IsStatement UStatement where
  type Var UStatement = MultiVar
  type Act UStatement = U
  type Out UStatement = A
  makeStatementParser = fmap UStatement . unrestrictedStatementParser
  evalStatement = evalUnrestrictedStatement . getUStatement

type Bot = Def AAStatement
type Agent = Def AUStatement
type Universe = Def UStatement

data NameInEnv = NameInEnv
  { nameInEnv :: Name
  , nameOfEnv :: Name
  } deriving (Eq, Ord, Read, Show)

data Controls = Control
  { ctrlShowFrames :: Bool
  , ctrlShowMap :: Bool
  , ctrlHidden :: Bool
  } deriving (Eq, Ord, Read, Show)

instance Parsable Controls where
  parser = do
    let pWith kw = P.keyword "with" *> P.keyword kw
    let toBool = maybe False (const True)
    (f, m) <- P.anyComboOf (pWith "frames") (pWith "map")
    h <- optional (P.keyword "hidden")
    return $ Control (toBool f) (toBool m) (toBool h)

data GameObject
  = Bot Bot
  | Agent Agent
  | Universe Universe
  | BotEnv Name [Call A A]
  | AgentEnv Name [Call A U]
  | UniverseEnv Name [Call U A]
  | Execute Action
  deriving Show

instance Parsable GameObject where
  parser
    = try (uncurry UniverseEnv <$> pEnv "universe" pconfUA)
    <|> try (uncurry AgentEnv <$> pEnv "agent" pconfAU)
    <|> try (uncurry BotEnv <$> pEnv "bot" pconfAA)
    <|> try (Universe <$> pAgent "universe" pconfUA)
    <|> try (Agent <$> pAgent "agent" pconfAU)
    <|> try (Bot <$> pOldschoolBot)
    <|> try (Bot <$> pAgent "bot" pconfAA)
    <|> (Execute <$> parser)
    where
      pEnv kw pconf = (,)
        <$> (P.keyword kw *> P.keyword "environment" *> P.anyname <* P.symbol ":")
        <*> ((callParser pconf `sepEndBy` P.comma) <* P.end)
      pAgent kw pconf = try pAgentMap <|> pAgentCode where
        pAgentCode = (P.keyword kw *> defheadParser pconf) <*> (codeParser pconf <* P.end)
        pAgentMap = (P.keyword kw *> P.keyword "map" *> defheadParser pconf) <*>
          (codeMapParser pconf <* P.end)
      pOldschoolBot = do
        P.keyword "bot"
        P.keyword "formula"
        name <- P.anyname
        P.symbol "="
        cStatement <- makeStatementParser pconfAA
        let dStatement = AAStatement $ S.Neg $ getAAStatement cStatement
        let code = FullMap $ Map.fromList [(A "C", cStatement), (A "D", dStatement)]
        return $ Def [] [] [] name code

data Action
  = Combat Name Controls Name Name
  | Compete Controls (Either NameInEnv (Call A A)) (Either NameInEnv (Call A A))
  | Play Controls (Either NameInEnv (Call U A)) [Either NameInEnv (Call A U)]
  deriving Show

instance Parsable Action where
  parser = try combatParser <|> try competeParser <|> playParser where
    combatParser = Combat
      <$> (P.keyword "combat" *> P.keyword "in" *> P.anyname)
      <*> (parser <* P.symbol ":")
      <*> (P.anyname <* P.comma)
      <*> (P.anyname <* P.end)
    competeParser = Compete
      <$> (P.keyword "compete" *> parser <* P.symbol ":")
      <*> (nameInEnvParser pconfAA <* P.comma)
      <*> (nameInEnvParser pconfAA <* P.end)
    playParser = Play
      <$> (P.keyword "compete" *> parser <* P.symbol ":")
      <*> (nameInEnvParser pconfUA <* P.comma)
      <*> ((nameInEnvParser pconfAU `sepEndBy` P.comma) <* P.end)

pconfAA :: PConf A A
pconfAA = PConf "@" "$" parser parser

pconfAU :: PConf A U
pconfAU = PConf "@" "$" parser parser

pconfUA :: PConf U A
pconfUA = PConf "$" "@" parser parser

nameInEnvParser :: PConf x y -> Parser (Either NameInEnv (Call x y))
nameInEnvParser pconf = try (Left <$> nie) <|> (Right <$> callParser pconf) where
  nie = NameInEnv
    <$> (P.anyname <* P.keyword "in")
    <*> P.anyname

data Setting = Setting
  { bots :: Map Name Bot
  , agents :: Map Name Agent
  , universes :: Map Name Universe
  , botEnvs :: Map Name [Call A A]
  , agentEnvs :: Map Name [Call A U]
  , universeEnvs :: Map Name [Call U A]
  } deriving Show

instance Blockable Setting where
  blockLines setting =
    [ (0, line "Bots" bots)
    , (0, line "Agents" agents)
    , (0, line "Universes" universes)
    , (0, line "Bot environments" botEnvs)
    , (0, line "Agent environments" agentEnvs)
    , (0, line "Universe environments" universeEnvs) ]
    where
      line :: String -> (Setting -> Map Name x) -> Text
      line x m = Text.pack $ printf "%s: %s" x $ renderArgs id $ Map.keys $ m setting

actions :: [GameObject] -> [Action]
actions objects = [x | Execute x <- objects]

mergeSettings :: SettingErrorM m => Setting -> Setting -> m Setting
mergeSettings x y = do
  bs <- mergeMap (DefNameCollision BotT) (bots x) (bots y)
  as <- mergeMap (DefNameCollision AgentT) (agents x) (agents y)
  us <- mergeMap (DefNameCollision UniverseT) (universes x) (universes y)
  bes <- mergeMap (EnvNameCollision BotT) (botEnvs x) (botEnvs y)
  bas <- mergeMap (EnvNameCollision AgentT) (agentEnvs x) (agentEnvs y)
  bus <- mergeMap (EnvNameCollision UniverseT) (universeEnvs x) (universeEnvs y)
  return $ Setting bs as us bes bas bus
  where
    mergeMap :: SettingErrorM m =>
      (Name -> SettingError) -> Map Name x -> Map Name x -> m (Map Name x)
    mergeMap err a b = do
      unless (Set.null (keySet a `Set.intersection` keySet b))
        (throwError $ err $ fromJust $ firstDup (Map.keys a ++ Map.keys b))
      return $ a `Map.union` b
    keySet = Set.fromList . Map.keys

ensureNoDuplicates :: SettingErrorM m => DefType -> Name -> [Call x y] -> m ()
ensureNoDuplicates t n = void . foldM addToMap Map.empty where
  addToMap m call
    | Map.member (callName call) m = throwError $ EnvCallCollision t n (callName call)
    | otherwise = return $ Map.insert (callName call) call m

gameToSetting :: SettingErrorM m => [GameObject] -> m Setting
gameToSetting = foldM addToSetting emptySetting where
  emptySetting = Setting Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty
  addToSetting setting@(Setting bs _ _ _ _ _) (Bot b) = do
    (when $ Map.member (defName b) bs) (throwError $ DefNameCollision BotT (defName b))
    return $ setting{bots=Map.insert (defName b) b bs}
  addToSetting setting@(Setting _ as _ _ _ _) (Agent a) = do
    (when $ Map.member (defName a) as) (throwError $ DefNameCollision AgentT (defName a))
    return $ setting{agents=Map.insert (defName a) a as}
  addToSetting setting@(Setting _ _ us _ _ _) (Universe u) = do
    (when $ Map.member (defName u) us) (throwError $ DefNameCollision UniverseT (defName u))
    return $ setting{universes=Map.insert (defName u) u us}
  addToSetting setting@(Setting _ _ _ env _ _) (BotEnv n calls) = do
    (when $ Map.member n env) (throwError $ EnvNameCollision BotT n)
    ensureNoDuplicates BotT n calls
    return $ setting{botEnvs=Map.insert n calls env}
  addToSetting setting@(Setting _ _ _ _ env _) (AgentEnv n calls) = do
    (when $ Map.member n env) (throwError $ EnvNameCollision AgentT n)
    ensureNoDuplicates AgentT n calls
    return $ setting{agentEnvs=Map.insert n calls env}
  addToSetting setting@(Setting _ _ _ _ _ env) (UniverseEnv n calls) = do
    (when $ Map.member n env) (throwError $ EnvNameCollision UniverseT n)
    ensureNoDuplicates UniverseT n calls
    return $ setting{universeEnvs=Map.insert n calls env}
  addToSetting setting (Execute _) = return setting

printVsHeader :: (Show x, Show y) => Controls -> Call x y -> Call y x -> IO ()
printVsHeader ctrls call1 call2 =
  (unless $ ctrlHidden ctrls)
    (printf "%s vs %s:\n" (show call1) (show call2))

printMultiHeader :: (Show x, Show y) => Controls -> Call x y -> [Call y x] -> IO ()
printMultiHeader ctrls call0 calls =
  (unless $ ctrlHidden ctrls)
    (printf "%s(%s):\n" (show call0) (renderArgs show calls))

printCompetitionTable :: Show v => Controls -> Map v (ModalFormula v) -> IO ()
printCompetitionTable ctrls cmap =
  (when $ ctrlShowMap ctrls && not (ctrlHidden ctrls))
    (displayTable $ indentTable "  " $ tuplesToTable $ Map.toAscList cmap)

printKripkeTable :: (Ord v, Show v) => Controls -> Map v (ModalFormula v) -> IO ()
printKripkeTable ctrls cmap =
  (when $ ctrlShowFrames ctrls && not (ctrlHidden ctrls))
    (displayTable $ indentTable "  " $ kripkeTable cmap)

printVsResults :: (Show x, Show y, Show a, Show b) =>
  Controls -> Call x y -> a -> Call y x -> b -> IO ()
printVsResults ctrls call1 r1 call2 r2 =
  (unless $ ctrlHidden ctrls)
    (printf "  Result: %s=%s, %s=%s\n\n"
      (callHandle call1) (show r1)
      (callHandle call2) (show r2))

printMultiResults :: (Show a, Show b, Show x, Show y) =>
  Controls -> Call x y -> a -> [Call y x] -> [b] -> IO ()
printMultiResults ctrls call0 r0 calls rs =
  (unless $ ctrlHidden ctrls)
    (printf "  Result: %s=%s, %s\n\n"
      (callHandle call0) (show r0)
      (renderArgs (uncurry renderPlays) (zip calls rs)))
  where renderPlays c r = printf "%s=%s" (callHandle c) (show r) :: String

runCompetition2 :: (Ord x, Ord y, Show x, Show y) =>
  Controls -> Call x y -> Call y x -> (Name -> Name -> IO (Competition x y)) -> IO ()
runCompetition2 ctrls call1 call2 getCmap = do
  (printVsHeader ctrls call1 call2)
  cmap <- getCmap (callHandle call1) (callHandle call2)
  let (r1, r2) = resolve2 (callHandle call1) (callHandle call2) cmap
  (printCompetitionTable ctrls cmap)
  (printKripkeTable ctrls cmap)
  (printVsResults ctrls call1 r1 call2 r2)

data UncompiledEnv s = UncompiledEnv
  { _envtype :: DefType
  , _envname :: Name
  , _cdlist :: [(Def s, Call (Act s) (Out s))] }

setAOs :: (IsStatement s, Functor m, MonadError SettingError m) =>
  [Act s] -> [Out s] -> UncompiledEnv s -> m (UncompiledEnv s)
setAOs as os env = (\cds -> env{_cdlist=cds}) <$> newCDlist where
  newCDlist = mapM (uncurry setAO) (_cdlist env)
  compileErr = throwError . WrapC
  setList _ _ [] news = return news
  setList _ _ olds [] = return olds
  setList t n olds news
    | Set.fromList olds == Set.fromList news = return olds
    | otherwise = throwError $ ListMismatch t n (map show olds) (map show news)
  setAO def call = do
    (as', os') <- either compileErr return $ runExcept (defcallAOlists def call)
    as'' <- setList ActionT (callName call) as' as
    os'' <- setList OutcomeT (callName call) os' os
    return (def, call{callActions=as'', callOutcomes=os''})

getAOs :: (IsStatement s, Functor m, Applicative m, MonadError SettingError m) =>
  Name -> UncompiledEnv s -> m ([Act s], [Out s])
getAOs name env = foldM joinAOs ([], []) (_cdlist env) >>= preferMainOrdering where
  findMain = List.find (\(_, c) -> callHandle c == name) (_cdlist env)
  leftBias xs ys = if null xs then ys else xs
  unknownErr = throwError $ UnknownEnvCall (_envtype env) (_envname env) name
  compileErr = throwError . WrapC
  preferMainOrdering (as, os) = do
    (def, call) <- maybe unknownErr return findMain
    (as', os') <- either compileErr return $ runExcept (defcallAOlists def call)
    return (leftBias as' as, leftBias os' os)
  joinAOs (as, os) (def, call) = do
    (as', os') <- either compileErr return $ runExcept (defcallAOlists def call)
    (,) <$> ensureMatches ActionT as' as <*> ensureMatches OutcomeT os' os
    where
      ensureMatches :: (Eq x, Ord x, Show x, MonadError SettingError m) =>
        ValType -> [x] -> [x] -> m [x]
      ensureMatches _ xs [] = return xs
      ensureMatches _ [] ys = return ys
      ensureMatches t xs ys
        | Set.fromList xs == Set.fromList ys = return ys
        | otherwise = throwError (ListMismatch t (callName call) (map show xs) (map show ys))

compileEnv :: (IsStatement s, MonadError SettingError m) =>
  UncompiledEnv s -> m (Env (Var s) (Act s) (Out s))
compileEnv = foldM addToEnv nobody . _cdlist where
  addToEnv env (def, call) = do
    let compileErr = throwError . WrapC
    let envErr = throwError . WrapE
    code <- either compileErr return (compile def call)
    either envErr return (insert env (callHandle call) code)

findDef :: MonadError SettingError m =>
  DefType -> Map Name (Def s) -> Name -> m (Def s)
findDef t dmap dname = maybe noSuchDef return (Map.lookup dname dmap) where
  noSuchDef = throwError $ UnknownDef t dname

makeUEnv :: (IsStatement s, MonadError SettingError m) =>
  DefType ->
  Map Name (Def s) ->
  Map Name [Call (Act s) (Out s)] ->
  Either NameInEnv (Call (Act s) (Out s)) ->
  m (Call (Act s) (Out s), UncompiledEnv s)
makeUEnv t dmap emap (Left (NameInEnv nameIn nameOf)) = do
  env <- getUEnv t dmap emap nameOf
  call <- findCall env nameIn
  return (call, env)
makeUEnv t dmap _ (Right call)  = do
  let name = callName call
  def <- findDef t dmap name
  return (call, UncompiledEnv t (printf "[autoenv %s]" name) [(def, call)])

getUEnv :: MonadError SettingError m =>
  DefType ->
  Map Name (Def s) ->
  Map Name [Call (Act s) (Out s)] ->
  Name ->
  m (UncompiledEnv s)
getUEnv t dmap emap ename = do
  let noSuchEnv = throwError $ UnknownEnv t ename
  calls <- maybe noSuchEnv return (Map.lookup ename emap)
  defs <- mapM (findDef t dmap . callName) calls
  return $ UncompiledEnv t ename (zip defs calls)

findCall :: (IsStatement s, MonadError SettingError m) =>
  UncompiledEnv s -> Name -> m (Call (Act s) (Out s))
findCall env cname = maybe unknownCall (return . snd) getCall where
  getCall = List.find (\(_, c) -> callHandle c == cname) (_cdlist env)
  unknownCall = throwError $ UnknownEnvCall (_envtype env) (_envname env) cname

executeAction :: Setting -> Action -> IO ()
executeAction setting (Combat nenv ctrls n1 n2) = do
  env <- run $ setAOs cd cd =<< getUEnv BotT (bots setting) (botEnvs setting) nenv
  call1 <- run $ findCall env n1
  call2 <- run $ findCall env n2
  cenv <- run $ compileEnv env
  runCompetition2 ctrls call1 call2 (prunedCmap cenv)
  where
    cd = [A "C", A "D"]
    prunedCmap env = (fmap removeDvars . run) .: competitionMap env
    removeDvars = Map.filterWithKey (const . varIsC) . Map.map negateDs
    varIsC (Vs1 _ _ (A "C")) = True
    varIsC (Vs2 _ _ (A "C")) = True
    varIsC _ = False
    negateDs m = m >>= cify where
      cify (Vs1 x1 x2 (A "D")) = Neg (Var $ Vs1 x1 x2 $ A "C")
      cify (Vs2 x1 x2 (A "D")) = Neg (Var $ Vs2 x1 x2 $ A "C")
      cify x = Var x
executeAction setting (Compete ctrls ref1 ref2) = do
  (call1, env1) <- run $ makeUEnv BotT (bots setting) (botEnvs setting) ref1
  (call2, env2) <- run $ makeUEnv BotT (bots setting) (botEnvs setting) ref2
  (as1, os1) <- run $ getAOs (callName call1) env1
  (as2, os2) <- run $ getAOs (callName call2) env2
  env1' <- run $ setAOs os2 as2 env1
  env2' <- run $ setAOs os1 as1 env2
  call1' <- run $ findCall env1' (callName call1)
  call2' <- run $ findCall env2' (callName call2)
  cenv1 <- run $ compileEnv env1'
  cenv2 <- run $ compileEnv env2'
  runCompetition2 ctrls call1' call2' (run .: competitionMap2 cenv1 cenv2)
executeAction setting (Play ctrls uref arefs) = do
  let uMakeEnv = makeUEnv UniverseT (universes setting) (universeEnvs setting)
  let aMakeEnv = makeUEnv AgentT (agents setting) (agentEnvs setting)
  (uCall, uEnv) <- run $ uMakeEnv uref
  (aCalls, aEnvs) <- run $ unzip <$> mapM aMakeEnv arefs
  (uas, uos) <- run $ getAOs (callName uCall) uEnv
  aAOslist <- run $ sequence (zipWith (\c e -> getAOs (callName c) e) aCalls aEnvs)
  uEnv' <- run $ foldM (\ue (aas, aos) -> setAOs aos aas ue) uEnv aAOslist
  aEnvs' <- run $ mapM (setAOs uos uas) aEnvs
  uCall' <- run $ findCall uEnv' (callName uCall)
  aCalls' <- run $ mapM (\(c, e) -> findCall e (callName c)) (zip aCalls aEnvs')
  (printMultiHeader ctrls uCall' aCalls')
  uCEnv <- run $ compileEnv uEnv'
  aCEnvs <- run $ mapM compileEnv aEnvs'
  let upair = (callHandle uCall', uCEnv)
  let apairs = zip (map callHandle aCalls') aCEnvs
  cmap <- run $ multiCompetition upair apairs
  (uResult, aResults) <- run (multiCompete upair apairs)
  (printCompetitionTable ctrls cmap)
  (printKripkeTable ctrls cmap)
  (printMultiResults ctrls uCall uResult aCalls aResults)

gameParser :: Parser [GameObject]
gameParser = (parser `sepEndBy` P.w) <* eof

parseFile :: FilePath -> IO [GameObject]
parseFile path = runFile (parse gameParser path) path

compileFile :: FilePath -> IO Setting
compileFile path = run . gameToSetting =<< parseFile path

playGame :: [GameObject] -> IO ()
playGame game = do
  setting <- run $ gameToSetting game
  putStrLn "Setting:"
  displayBlock' "  " setting
  putStrLn "Loaded. Executing..."
  putStrLn ""
  mapM_ (executeAction setting) (actions game)

playFile :: FilePath -> IO ()
playFile path = parseFile path >>= playGame

playGame' :: Setting -> [GameObject] -> IO ()
playGame' base game = do
  putStrLn "Setting loaded from other files:"
  displayBlock' "  " base
  local <- run $ gameToSetting game
  putStrLn "Setting from this file:"
  displayBlock' "  " local
  setting <- run $ mergeSettings base local
  putStrLn "Merged. Executing..."
  putStrLn ""
  mapM_ (executeAction setting) (actions game)

playFile' :: FilePath -> Setting -> IO ()
playFile' path setting = parseFile path >>= playGame' setting
