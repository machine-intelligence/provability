{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module Modal.Universes where
import Prelude hiding (mapM, sequence, foldr)
import Control.Applicative
import Control.Monad.Identity hiding (mapM, mapM_, sequence)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import Data.Text (Text)
import Data.Traversable
import Modal.Code
import Modal.Competition
import Modal.Display
import Modal.Environment hiding (NameCollision) -- TODO
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

data MultiVar u a = UPlays u | ANPlays Int a | ANPlaysVs Int Name a deriving (Eq, Ord)
instance (Show a, Show o) => Show (MultiVar a o) where
  show (UPlays u) = printf "U(...)%s" (show u)
  show (ANPlays i a) = printf "A%d(U)%s" i (show a)
  show (ANPlaysVs i other a) = printf "A%d(%s)%s" i other (show a)
instance Bifunctor MultiVar where
  bimap f g = runIdentity . bitraverse (Identity . f) (Identity . g)
instance Bifoldable MultiVar where
  bifoldMap f _ (UPlays u) = f u
  bifoldMap _ g (ANPlays _ a) = g a
  bifoldMap _ g (ANPlaysVs _ _ a) = g a
instance Bitraversable MultiVar where
  bitraverse f _ (UPlays u) = UPlays <$> f u
  bitraverse _ g (ANPlays i a) = ANPlays i <$> g a
  bitraverse _ g (ANPlaysVs i other a) = ANPlaysVs i other <$> g a
instance AgentVar MultiVar where
  makeAgentVarParser u a = try uvp <|> try pvu <|> try pvo <?> "a variable" where
    uvp = (\(_, _, x) -> UPlays x)  <$> vs (string "U") (pure ()) u
    pvu = (\(n, _, x) -> ANPlays n x) <$> vs anum (option () $ void $ string "U") a
    pvo = (\(n, o, x) -> ANPlaysVs n o x) <$> vs anum P.anyname a
    vs x y z = (,,) <$> x <*> P.parens y <*> z
    anum = string "A" *> option 1 parser
instance (Parsable u, Parsable a) => Parsable (MultiVar u a) where
  parser = makeAgentVarParser parser parser
instance (Parsable u, Parsable a) => Read (MultiVar u a) where
  readsPrec _ s = case parse (parser <* eof) "reading MultiVar" (Text.pack s) of
    Right result -> [(result,"")]
    Left err -> error $ show err
instance Canonicalizable2 MultiVar where
  canonicalize2 v1 v2 = fmap expandName where
    expandName (UPlays val) = v1 val
    expandName (ANPlays _ val) = v2 Nothing val
    expandName (ANPlaysVs _ other val) = v2 (Just other) val
instance IsMultiVarU MultiVar where
  promoteU names (UPlays x) = UniversePlays names x
  promoteU names (ANPlays i x) = PlayerNPlays names i x
  promoteU names (ANPlaysVs i other x) = PlayerNPlays (alter names 0 $ const other) i x

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

data Action
  = Combat Name Controls Name Name
  | Compete Controls (Either NameInEnv (Call A A)) (Either NameInEnv (Call A A))
  | Play Controls (Either NameInEnv (Call U A)) [Either NameInEnv (Call A U)]
  deriving Show

data Setting = Setting
  { bots :: Map Name Bot
  , agents :: Map Name Agent
  , universes :: Map Name Universe
  -- NOTE: You need to ensure that there are no dups when you create the settings.
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

-- TODO: This string passing thing has to stop.
compileCall :: IsStatement s =>
  String ->
  Map Name (Def s) ->
  Call (Act s) (Out s) ->
  Either SettingError (CompiledAgent s)
compileCall err defs call = do
  def <- maybe (Left $ Unknown err $ callName call) Right (Map.lookup (callName call) defs)
  either (Left . CompileErr) Right $ compile def call

findEnv :: String -> Map Name [Call x y] -> Name -> Either SettingError [Call x y]
findEnv err emap ename = maybe (Left unknownEnv) Right (Map.lookup ename emap) where
  unknownEnv = Unknown (err ++ " environment") ename

findCall :: (Show x, Show y) => String -> [Call x y]-> Name -> Either SettingError (Call x y)
findCall err clist cname = maybe (Left unknownDef) Right (List.find isCall clist) where
  isCall call = callHandle call == cname
  unknownDef = Unknown err cname

ensureNoDuplicates :: String -> [Call x y] -> Either SettingError ()
ensureNoDuplicates err = void . foldM addToMap Map.empty where
  addToMap m call
    | Map.member (callName call) m = Left $ NameCollision err (callName call)
    | otherwise = return $ Map.insert (callName call) call m

gameToSetting :: [GameObject] -> Either SettingError Setting
gameToSetting = foldM addToSetting emptySetting where
  emptySetting = Setting Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty
  addToSetting setting@(Setting bs _ _ _ _ _) (Bot b) = do
    (when $ Map.member (defName b) bs) (Left $ NameCollision "bot" (defName b))
    return $ setting{bots=Map.insert (defName b) b bs}
  addToSetting setting@(Setting _ as _ _ _ _) (Agent a) = do
    (when $ Map.member (defName a) as) (Left $ NameCollision "agent" (defName a))
    return $ setting{agents=Map.insert (defName a) a as}
  addToSetting setting@(Setting _ _ us _ _ _) (Universe u) = do
    (when $ Map.member (defName u) us) (Left $ NameCollision "universe" (defName u))
    return $ setting{universes=Map.insert (defName u) u us}
  addToSetting setting@(Setting _ _ _ env _ _) (BotEnv n calls) = do
    ensureNoDuplicates ("bot environment " ++ n) calls
    return $ setting{botEnvs=Map.insert n calls env}
  addToSetting setting@(Setting _ _ _ _ env _) (AgentEnv n calls) = do
    ensureNoDuplicates ("agent environment " ++ n) calls
    return $ setting{agentEnvs=Map.insert n calls env}
  addToSetting setting@(Setting _ _ _ _ _ env) (UniverseEnv n calls) = do
    ensureNoDuplicates ("universe environment " ++ n) calls
    return $ setting{universeEnvs=Map.insert n calls env}
  addToSetting setting (Execute _) = return setting

-- TODO: Refactor error handling throughout.
data SettingError
  = Unknown String Name
  | EnvErr EnvError
  | CompileErr CompileError
  | ArgMismatch Name
  | NameCollision String Name
instance Show SettingError where
  show (Unknown s n) = printf "Unknown %s: %s" s n
  show (EnvErr e) = show e
  show (CompileErr e) = show e
  show (ArgMismatch n) = printf "Arg mismatch for %s" n
  show (NameCollision s n) = printf "%s name collision: %s" s n

fromEnv :: (Show x, Show y) =>
  String -> Map Name [Call x y] -> NameInEnv ->
  Either SettingError (Call x y, [Call x y])
fromEnv err getEnv (NameInEnv nameIn nameOf) = do
  let noSuchEnv = Unknown (err ++ " environment") nameOf
  let noSuchDef = Unknown (err ++ " in environment" ++ nameOf) nameIn
  calls <- maybe (Left noSuchEnv) Right (Map.lookup nameIn getEnv)
  case span (\call -> callHandle call /= nameIn) calls of
    (predecessors, call : _) -> return (call, predecessors)
    _ -> Left noSuchDef

toEnv :: (Show (Act s), Show (Out s), IsStatement s) =>
  String -> Map Name (Def s) -> [Call (Act s) (Out s)] ->
  Either SettingError (Env (Var s) (Act s) (Out s))
toEnv err lookupDef = foldM addToEnv nobody where
  addToEnv env call = compileCall err lookupDef call >>= insertCall env call
  insertCall env call = either (Left . EnvErr) Right . insert env (callHandle call)

-- TODO: Use MonadExcept, forgo the need for "run".
-- TODO: error messages here are bad and hard-coded.
getAOLists :: Call x y -> Either SettingError ([x], [y])
getAOLists call = case (callActions call, callOutcomes call) of
  (Just xs, Just ys) -> return (xs, ys)
  (Nothing, Nothing) -> Left (Unknown "arguments and outcomes for" $ callName call)
  (Nothing, _) -> Left (Unknown "arguments for" $ callName call)
  _ -> Left (Unknown "outcomes for" $ callName call)


setAOLists :: (Ord x, Ord y) => ([x], [y]) -> Call x y -> Either SettingError (Call x y)
setAOLists (xs, ys) call = do
  as <- ensureMatch xs (callActions call)
  os <- ensureMatch ys (callOutcomes call)
  return call{callActions=Just as, callOutcomes=Just os}
  where
    ensureMatch :: Ord a => [a] -> Maybe [a] -> Either SettingError [a]
    ensureMatch as Nothing = return as
    ensureMatch as (Just bs)
      | Set.fromList as == Set.fromList bs = return bs
      | otherwise = Left $ ArgMismatch $ callName call

-- TODO: This should make call of defcallAOlists, I'm pretty sure.
matchAOLists :: (Ord x, Ord y) =>
  Call x y -> Call y x -> Either SettingError (Call x y, Call y x, [x], [y])
matchAOLists call1 call2 = do
  (as1, os2) <- matchLists (callActions call1) (callOutcomes call2)
  (os1, as2) <- matchLists (callOutcomes call1) (callActions call2)
  let call1' = call1{callActions=Just as1, callOutcomes=Just os1}
  let call2' = call2{callActions=Just as2, callOutcomes=Just os2}
  return (call1', call2', as1, as2)
  where
    matchLists :: Ord a => Maybe [a] -> Maybe [a] -> Either SettingError ([a], [a])
    matchLists Nothing Nothing =
      Left $ Unknown ("args/outcomes in") (callName call1 ++ " or " ++ callName call2)
    matchLists (Just xs) (Just ys)
      | Set.fromList xs == Set.fromList ys = return (xs, ys)
      | otherwise = Left $ ArgMismatch (callName call1 ++ " and " ++ callName call2)
    matchLists (Just xs) Nothing = return (xs, xs)
    matchLists Nothing (Just ys) = return (ys, ys)

toCallList :: (Show x, Show y) =>
  String ->
  Map Name [Call x y] ->
  Either NameInEnv (Call x y) ->
  Either SettingError (Call x y, [Call x y])
toCallList err getEnv (Left nie) = fromEnv err getEnv nie
toCallList _ _ (Right call) = return (call, [])

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

executeAction :: Setting -> Action -> IO ()
executeAction setting (Combat nenv ctrls n1 n2) = do
  calls <- run $ findEnv "bot" (botEnvs setting) nenv
  calls' <- run $ mapM (setAOLists (cd, cd)) calls
  call1 <- run $ findCall ("bot in " ++ nenv) calls' n1
  call2 <- run $ findCall ("bot in " ++ nenv) calls' n2
  env <- run $ toEnv "bot" (bots setting) calls'
  runCompetition2 ctrls call1 call2 (prunedCmap env)
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
  (call1, calls1) <- run $ toCallList "bot" (botEnvs setting) ref1
  (call2, calls2) <- run $ toCallList "bot" (botEnvs setting) ref2
  (call1', call2', as1, as2) <- run $ matchAOLists call1 call2
  calls1' <- run $ mapM (setAOLists (as1, as2)) calls1
  calls2' <- run $ mapM (setAOLists (as2, as1)) calls2
  env1 <- run $ toEnv "bot" (bots setting) (calls1' ++ [call1'])
  env2 <- run $ toEnv "bot" (bots setting) (calls2' ++ [call2'])
  runCompetition2 ctrls call1 call2 (run .: competitionMap2 env1 env2)
executeAction setting (Play ctrls uref arefs) = do
  let getUCallList = toCallList "universe" (universeEnvs setting)
  let getACallList = toCallList "agent" (agentEnvs setting)
  (uCall, rawUCallList) <- run $ getUCallList uref
  (rawACalls, rawACallLists) <- run $ unzip <$> mapM getACallList arefs
  aoLists <- run $ getAOLists uCall
  uCallList <- run $ mapM (setAOLists aoLists) rawUCallList
  aCalls <- run $ mapM (setAOLists $ swap aoLists) rawACalls
  aCallLists <- run $ mapM (mapM (setAOLists $ swap aoLists)) rawACallLists
  (printMultiHeader ctrls uCall aCalls)
  let toUEnv c cs = toEnv "universe" (universes setting) (cs ++ [c])
  let toAEnv c cs = toEnv "agent" (agents setting) (cs ++ [c])
  uEnv <- run $ toUEnv uCall uCallList
  aEnvs <- run $ sequence $ zipWith toAEnv aCalls aCallLists
  let upair = (callHandle uCall, uEnv)
  let apairs = zip (map callHandle aCalls) aEnvs
  cmap <- run $ multiCompetition upair apairs
  (uResult, aResults) <- run (multiCompete upair apairs)
  (printCompetitionTable ctrls cmap)
  (printKripkeTable ctrls cmap)
  (printMultiResults ctrls uCall uResult aCalls aResults)

gameParser :: Parser [GameObject]
gameParser = (parser `sepEndBy` P.w) <* eof

parseFile :: FilePath -> IO [GameObject]
parseFile path = runFile (parse gameParser path) path

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

{-
-- TODO: This needs refactoring. It should probably go into Code.hs somehow.
-- Also, the syntax is quite bad; consider removing the need for a "where" and
-- for the semicolons.
universeMapParser :: Parsec Text u (Def UStatement)
universeMapParser = do
  n <- P.keyword "umap" *> P.name
  ps <- option [] (try $ defargsParser parser parser)
  (as, os) <- defordersParser "outcomes" "actions" parser parser
  P.keyword "where"
  c <- FullMap <$> codeMapParser parser parser
  P.keyword "end"
  return $ Def ps as os n c

gameobject
parser =   try (env "universe")
       <|> try (env "agent")
       <|> try (env "bot")
       <|> try (Universe <$> universe)
       <|> try (Agent <$> agent)
       <|> try (Bot <$> bot)
       <|> try (Action <$> parser)
       where
        env = xxx environment {name} {calls} end
        universe = try universeMap <|> universeDef
        agent = try agentMap <|> agentDef
        bot = try pdbot <|> try botMap <|> try botDef

action
parser =
  combat in {call} [with map|with frames|hidden]: {call}, {call} (.|end)
  compete [with map|with frames|hidden]: {call}, {call} (.|end)
  challenge [with map|with frames|hidden]: {call}, [call, ...] (.|end)
-}
