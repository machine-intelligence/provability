{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
module Modal.Combat where
import Prelude hiding (mapM, sequence, foldr)
import Control.Applicative
import Control.Monad.Except hiding (mapM, mapM_, sequence)
import Data.Maybe
import Data.Map (Map)
import Data.Traversable
import Modal.CompilerBase
import Modal.Code
import Modal.Def
import Modal.Competition
import Modal.Display
import Modal.Formulas
import Modal.Parser (Parsable, parser)
import Modal.Utilities
import Text.Parsec hiding ((<|>), optional, many, State)
import Text.Parsec.Text
import Text.Printf (printf)
import Text.Read (readMaybe)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Modal.Parser as P
import qualified Modal.Statement as S

-------------------------------------------------------------------------------

data CorD = C | D deriving (Eq, Ord, Enum, Read, Show)

-------------------------------------------------------------------------------

data CombatVar m t = MeVsThemIs m | ThemVsIs (Maybe Call) t deriving (Eq, Ord)

instance (Show a, Show o) => Show (CombatVar a o) where
  show (MeVsThemIs m) = printf "Me(Them)=%s" (show m)
  show (ThemVsIs Nothing t) = printf "Them(Me)=%s" (show t)
  show (ThemVsIs (Just o) t) = printf "Them(%s)%s" (show o) (show t)

instance (Parsable m, Parsable t) => Parsable (CombatVar m t) where
  parser = try mvt <|> try tvm <|> try tvo <?> "a variable" where
    mvt = MeVsThemIs . snd <$> vs (string "Me") (nilOr "Them") parser
    tvm = ThemVsIs Nothing . snd <$> vs (string "Them") (nilOr "Me") parser
    tvo = uncurry (ThemVsIs . Just) <$> vs (string "Them") parser parser
    vs x y z = (,) <$> (x *> P.parens y) <*> z
    nilOr = option () . void . string

instance (Parsable u, Parsable a) => Read (CombatVar u a) where
  readsPrec _ s = case parse (parser <* eof) "reading CombatVar" (Text.pack s) of
    Right result -> [(result,"")]
    Left err -> error $ show err

instance ModalCombatVar CombatVar where
  subagentsIn (ThemVsIs (Just x) _) = Set.singleton x
  subagentsIn _ = Set.empty

  makeModalVar v1 _ (MeVsThemIs m) = v1 m
  makeModalVar _ v2 (ThemVsIs o t) = v2 o t

-------------------------------------------------------------------------------

data AVar a u = AMe a | AThem u deriving (Eq, Ord)

instance (Show a, Show u) => Show (AVar a u) where
  show (AMe a) = printf "A()%s" (show a)
  show (AThem u) = printf "U()%s" (show u)

instance MultiVarA AVar where
  promoteA i (AMe a) = PlayerNPlays i a
  promoteA _ (AThem u) = UniversePlays u

-------------------------------------------------------------------------------

data UVar u a = UMe u | UThem Int a deriving (Eq, Ord)

instance (Show a, Show u) => Show (UVar a u) where
  show (UMe u) = printf "U()%s" (show u)
  show (UThem n a) = printf "A%d()%s" n (show a)

instance MultiVarU UVar where
  promoteU (UMe u) = UniversePlays u
  promoteU (UThem n a) = PlayerNPlays n a

-------------------------------------------------------------------------------

data Controls = Controls
  { ctrlShowFrames :: Bool
  , ctrlShowMap :: Bool
  , ctrlHidden :: Bool
  } deriving (Eq, Ord, Read)

instance Show Controls where
  show (Controls f m h) = "<" ++
    (if f then "F" else "") ++
    (if m then "M" else "") ++
    (if h then "H" else "") ++ ">"

instance Parsable Controls where
  parser = do
    let pWith kw = P.keyword "with" *> P.keyword kw
    (f, m) <- P.anyComboOf (pWith "frames") (pWith "map")
    h <- optional (P.keyword "hidden")
    return $ Controls (isJust f) (isJust m) (isJust h)

-------------------------------------------------------------------------------

data GameObject
  = Agent Def
  | Theory Def
  | Problem Def [Value] [[Value]]
  | Execute Action
  deriving Show

instance Parsable GameObject where
  parser
    =   pProblem
    <|> (Theory <$> defParser theoryDConf)
    <|> (Agent <$> defParser agentDConf)
    <|> (Agent <$> pOldschoolBot)
    <|> (Execute <$> parser)
    where
      problemDConf = DefConfig "problem" True "outcome" "outcomes" "action" "actions"
      theoryDConf = DefConfig "theory" False "action" "actions" "outcome" "outcomes"
      agentDConf = DefConfig "agent" False "action" "actions" "response" "responses"
      pProblem = (\(d, (v, vs)) -> Problem d v vs) <$>
        defParserWithExtras pValues problemDConf
      pValues = (,) <$> valuesParser <*> many1 valuesParser
      valuesParser = try vals <|> try dunno where
        vals = P.brackets (parser `sepEndBy` P.comma)
        dunno = P.brackets (string "...") $> []
      pOldschoolBot = do
        P.keyword "bot"
        name <- P.valueStr
        P.symbol "="
        rawStatement <- parser
        let actTable = [("C", rawStatement), ("D", S.Neg rawStatement)]
        return $ Def [] name (ActionMap $ Map.fromList actTable)

-------------------------------------------------------------------------------

data Action
  = Combat Controls Call Call
  | Compete Controls Call Call
  | Play Controls Call [Call]
  deriving Show

instance Parsable Action where
  parser = combatParser <|> competeParser <|> playParser where
    combatParser = Combat
      <$> (P.keyword "combat" *> parser <* P.symbol "!")
      <*> (parser <* P.keyword "vs")
      <*> parser
    competeParser = Compete
      <$> (P.keyword "compete" *> parser <* P.symbol ":")
      <*> (parser <* P.keyword "vs")
      <*> parser
    playParser = Play
      <$> (P.keyword "play" *> parser <* P.symbol ":")
      <*> (parser <* P.powerComma)
      <*> ((parser `sepEndBy` P.powerComma) <* P.symbol ".")

-------------------------------------------------------------------------------

data Setting = Setting
  { settingName :: Name
  , agents :: Map Name Def
  , theories :: Map Name Def
  , problems :: Map Name (Def, [Value], [[Value]])
  } deriving Show

instance Blockable Setting where
  blockLines setting =
    [ (0, Text.pack $ printf "%s:" $ settingName setting)
    , (1, Text.pack $ line "Agents" agents)
    , (1, Text.pack $ line "Theories" theories)
    , (1, Text.pack $ line "Problems" problems) ]
    where line :: String -> (Setting -> Map Name x) -> String
          line x m = printf "%s: %s" x $ renderArgs id $ Map.keys $ m setting

mergeSettingsR :: MonadError FileError m => Setting -> Setting -> m Setting
mergeSettingsR x y = do
  as <- mergeMap (NameCollision AgentT) (agents x) (agents y)
  ts <- mergeMap (NameCollision TheoryT) (theories x) (theories y)
  ps <- mergeMap (NameCollision ProblemT) (problems x) (problems y)
  return $ Setting (settingName y) as ts ps
  where mergeMap err a b = case firstDup (Map.keys a ++ Map.keys b) of
          Nothing -> return $ a `Map.union` b
          Just dup -> throwError (err dup)

-------------------------------------------------------------------------------

lookupDef :: MonadError FileError m => DefType -> Map Name x -> Name -> m x
lookupDef t defs name = maybe errUnknown return (Map.lookup name defs) where
  errUnknown = throwError $ UnknownDef t name

lookupVal :: MonadError DefError m => ClaimType -> [(Value, x)] -> Value -> m x
lookupVal t table val = maybe errInvalid return (List.lookup val table) where
  errInvalid = throwError $ InvalidValue t val (map fst table)

lookupAndCompile :: (Ord a, MonadError RuntimeError m) =>
  Setting -> CompileConfig a (v a o) -> Call -> m (ModalAgent v a o)
lookupAndCompile setting conf call = do
  let compileErr = CompileErr $ settingName setting
  let fileErr = FileErr $ settingName setting
  def <- wrapError fileErr (lookupDef AgentT (agents setting) (callName call))
  wrapError compileErr (compile conf call def)

-------------------------------------------------------------------------------

printVsHeader :: Controls -> Call -> Call -> IO ()
printVsHeader ctrls call1 call2 =
  (unless $ ctrlHidden ctrls)
    (printf "%s vs %s:\n" (show call1) (show call2))

printMultiHeader :: Controls -> Call -> [Call] -> IO ()
printMultiHeader ctrls call0 calls = unless (ctrlHidden ctrls) doDisplay where
  doDisplay =
    (printf "%s as U vs\n    %s:\n" (show call0)
      (List.intercalate ",\n    " $ zipWith addAliases calls [1..]))
  addAliases :: Call -> Int -> String
  addAliases c d = printf "%s as A%s" (show c) (anum d)
  anum d = if length calls == 1 then "" else show d

printCompetitionTable :: Show v => Controls -> Map v (ModalFormula v) -> IO ()
printCompetitionTable ctrls cmap =
  (when $ ctrlShowMap ctrls && not (ctrlHidden ctrls))
    (displayTable $ indentTable "  " $ tuplesToTable $ Map.toAscList cmap)

printKripkeTable :: (Ord v, Show v) => Controls -> Map v (ModalFormula v) -> IO ()
printKripkeTable ctrls cmap =
  (when $ ctrlShowFrames ctrls && not (ctrlHidden ctrls))
    (displayTable $ indentTable "  " $ kripkeTable cmap)

printVsResults :: (Show a, Show b) => Controls -> Call -> a -> Call -> b -> IO ()
printVsResults ctrls call1 r1 call2 r2 =
  (unless $ ctrlHidden ctrls)
    (printf "  Result: %s=%s, %s=%s\n\n"
      (show call1) (show r1)
      (show call2) (show r2))

printMultiResults :: (Show a, Show b) =>
  Controls -> Call -> a -> [Call] -> [b] -> IO ()
printMultiResults ctrls call0 r0 calls rs = unless (ctrlHidden ctrls) doDisplay where
  doDisplay =
    (printf "  Result: U()=%s, %s\n\n" (show r0)
      (renderArgs id $ zipWith showAresult rs [1..]))
  showAresult :: Show b => b -> Int -> String
  showAresult r d = if length rs == 1
    then printf "A()=%s" (show r)
    else printf "A%d()=%s" d (show r)

-------------------------------------------------------------------------------

modalClaimValues :: ParsedClaim -> [(ClaimType, Value)]
modalClaimValues (ParsedClaim name _ rel) = case name of
  "Me" -> map (ActionT,) (mapMaybe lit $ relToMentions rel)
  "Them" -> map (OutcomeT,) (mapMaybe lit $ relToMentions rel)
  _ -> []

handleModalClaim :: MonadError DefError m =>
  [(Value, a)] -> [(Value, o)] -> CompiledClaim -> m (CombatVar a o)
handleModalClaim as os claim@(CompiledClaim name mcall mtype val) = handler where
  err = throwError . InvalidClaim claim
  mcall' = if mcall == Just (simpleCall "Me") then Nothing else mcall
  getAVal = lookupVal ActionT as val
  getOVal = lookupVal OutcomeT os val
  handler = do
    when (name `notElem` ["Me", "Them"])
      (err "claim must be about 'Me' or 'Them'")
    when (name == "Me" && mtype == Just OutcomeT)
      (err "'Me' returns actions, not responses")
    when (name == "Me" && isJust mcall && mcall /= Just (simpleCall "Them"))
      (err "cannot reason about what 'Me' would do against another")
    when (name == "Them" && mtype == Just ActionT)
      (err "'Them' returns responses, not actions")
    if name == "Me" then MeVsThemIs <$> getAVal else ThemVsIs mcall' <$> getOVal

modalCombatCConf :: (Show a, Show o) =>
  [(Value, a)] -> [(Value, o)] -> CompileConfig a (CombatVar a o)
modalCombatCConf aTable oTable = CompileConfig
  { availableActions = map fst aTable
  , availableOutcomes = map fst oTable
  , compileAction = lookupVal ActionT aTable
  , claimValues = modalClaimValues
  , handleClaim = handleModalClaim aTable oTable
  , finalizeFormula = \f -> do
      unless (isModalized f) (throwError $ IsUnmodalized $ show <$> f)
      return $ simplify f }

-------------------------------------------------------------------------------

problemClaimValues :: ParsedClaim -> [(ClaimType, Value)]
problemClaimValues (ParsedClaim name _ rel) = case name of
  "U" -> map (ActionT,) (mapMaybe lit $ relToMentions rel)
  _ -> map (OutcomeT,) (mapMaybe lit $ relToMentions rel)

handleProblemClaim :: MonadError DefError m =>
  [(Value, u)] -> [(Value, a)] -> CompiledClaim -> m (UVar u a)
handleProblemClaim us as claim@(CompiledClaim name mcall mtype val) = handler where
  err :: MonadError DefError m => String -> m a
  err = throwError . InvalidClaim claim
  getUVal = lookupVal ActionT us val
  getAVal = lookupVal OutcomeT as val
  notAnAgent = err "not a valid agent (use A1, A2, ...)"
  getPNum = case name of
    "U" -> return (0 :: Int)
    "A" -> return 1
    ('A':num) -> maybe notAnAgent return (readMaybe num)
    _ -> notAnAgent
  handler = do
    pnum <- getPNum
    when (name /= "U" && pnum < 1) (err "player numbers must be at least 1")
    when (name == "U" && isJust mcall)
      (err "cannot reason about self vs other agents")
    when (name /= "U" && isJust mcall)
      (err "universe cannot reason about agents vs other universes")
    -- This is correct. Don't be confused: problem "outcomes" are ActionT,
    -- and vice versa. (theory "outcomes" are OutcomeT. Someone has to be
    -- reversed. Or we could find better names for ActionT/OutcomeT.)
    when (name == "U" && mtype == Just OutcomeT)
      (err "'U' returns outcomes, not actions")
    when (name /= "U" && mtype == Just ActionT)
      (err "players returns actions, not outcomes")
    if pnum == 0 then UMe <$> getUVal else UThem pnum <$> getAVal

problemCConf :: [(Value, u)] -> [(Value, a)] -> CompileConfig u (UVar u a)
problemCConf uTable aTable = CompileConfig
  { availableActions = map fst uTable
  , availableOutcomes = map fst aTable
  , compileAction = lookupVal ActionT uTable
  , claimValues = problemClaimValues
  , handleClaim = handleProblemClaim uTable aTable
  , finalizeFormula = return . simplify }

-------------------------------------------------------------------------------

theoryClaimValues :: ParsedClaim -> [(ClaimType, Value)]
theoryClaimValues (ParsedClaim name _ rel) = case name of
  "A" -> map (ActionT,) (mapMaybe lit $ relToMentions rel)
  "U" -> map (OutcomeT,) (mapMaybe lit $ relToMentions rel)
  _ -> []

handleTheoryClaim :: MonadError DefError m =>
  [(Value, a)] -> [(Value, u)] -> CompiledClaim -> m (AVar a u)
handleTheoryClaim as us claim@(CompiledClaim name mcall mtype val) = handler where
  err = throwError . InvalidClaim claim
  getAVal = lookupVal ActionT as val
  getUVal = lookupVal OutcomeT us val
  handler = do
    when (name `notElem` ["A", "U"]) (err "invalid player (use A or U)")
    when (name == "A" && isJust mcall)
      (err "cannot reason about self in other universes")
    when (name == "U" && isJust mcall)
      (err "cannot reason about universe vs other agents")
    when (name == "A" && mtype == Just OutcomeT)
      (err "'A' returns actions, not outcomes")
    when (name == "U" && mtype == Just ActionT)
      (err "'U' returns outcomes, not actions")
    if name == "A" then AMe <$> getAVal else AThem <$> getUVal

theoryCConf :: (Show a, Show u) =>
  [(Value, a)] -> [(Value, u)] -> CompileConfig a (AVar a u)
theoryCConf aTable uTable = CompileConfig
  { availableActions = map fst aTable
  , availableOutcomes = map fst uTable
  , compileAction = lookupVal ActionT aTable
  , claimValues = theoryClaimValues
  , handleClaim = handleTheoryClaim aTable uTable
  , finalizeFormula = \f -> do
      unless (isModalized f) (throwError $ IsUnmodalized $ show <$> f)
      return $ simplify f }

-------------------------------------------------------------------------------

runModalCombat :: (Eq x, Eq y, Ord x, Ord y, Show x, Show y) =>
  Controls -> Call -> Call -> Competition x y -> IO ()
runModalCombat ctrls call1 call2 cmap = do
  let (r1, r2) = modalCombatResolve call1 call2 cmap
  printCompetitionTable ctrls cmap
  printKripkeTable ctrls cmap
  printVsResults ctrls call1 r1 call2 r2

executeAction :: Setting -> Action -> IO ()
executeAction setting = execute where
  -- Prisoner's dilemma competition
  execute (Combat ctrls call1 call2) = do
    printVsHeader ctrls call1 call2
    cmap <- run $ modalCombatMap1 (lookupAndCompile setting pdconf) call1 call2
    runModalCombat ctrls call1 call2 (removeDvars cmap)
  -- Modal agents referring to each other
  execute (Compete ctrls call1 call2) = do
    printVsHeader ctrls call1 call2
    def1 <- run $ findDef AgentT (agents setting) call1
    def2 <- run $ findDef AgentT (agents setting) call2
    let (as1, os1) = effectiveAOs modalClaimValues (defCode def1) call1
    let (as2, os2) = effectiveAOs modalClaimValues (defCode def2) call2
    let conf1 = modalCombatCConf (makeTable as1) (makeTable $ List.nub $ as2 ++ os1)
    let conf2 = modalCombatCConf (makeTable as2) (makeTable $ List.nub $ as1 ++ os2)
    let env1 = lookupAndCompile setting conf1
    let env2 = lookupAndCompile setting conf2
    cmap <- run $ modalCombatMap env1 env2 call1 call2
    runModalCombat ctrls call1 call2 cmap
  -- Unmodalized universe vs modalized agents
  execute (Play ctrls pCall tCalls) = do
    printMultiHeader ctrls pCall tCalls
    (pDef, oList, aLists) <- run $ findDef ProblemT (problems setting) pCall
    tDefs <- run $ mapM (findDef TheoryT (theories setting)) tCalls
    let (pAms, pOms) = effectiveAOs problemClaimValues (defCode pDef) pCall
    let pATable = makeTable $ if null oList then pAms else oList
    let pOTable = makeTable $ if all null aLists then pOms else concat aLists
    let pConf = problemCConf pATable pOTable
    let makeTableR xs ys = makeTable (if null xs then ys else xs)
    let { makeTConf def call aList =
      let (tAms, tOms) = effectiveAOs theoryClaimValues (defCode def) call
      in theoryCConf (makeTableR tAms aList) (makeTableR tOms oList) }
    let aLists' = if length aLists == 1 then repeat (head aLists) else aLists
    let tConfs = zipWith3 makeTConf tDefs tCalls aLists'
    let tCompile (conf, call, def) = wrapCErr $ compile conf call def
    p <- run $ wrapCErr $ compile pConf pCall pDef
    ts <- run $ mapM tCompile (zip3 tConfs tCalls tDefs)
    let cmap = multiCompetition p ts
    printCompetitionTable ctrls cmap
    printKripkeTable ctrls cmap
    let (pResult, tResults) = multiCompete p ts
    printMultiResults ctrls pCall pResult tCalls tResults
  -- Error wrappers
  wrapFErr :: MonadError RuntimeError m => Except FileError a -> m a
  wrapFErr = wrapError (FileErr $ settingName setting)
  wrapCErr :: MonadError RuntimeError m => Except CompileError a -> m a
  wrapCErr = wrapError (CompileErr $ settingName setting)
  -- Generic helper functions
  makeTable = map (\v -> (v, v))
  findDef t defs = wrapFErr . lookupDef t defs . callName
  -- Helpers specific to the prisoner's dilemma
  cdTable = [("C", C), ("D", D)]
  pdconf = modalCombatCConf cdTable cdTable
  removeDvars = Map.filterWithKey (const . varIsC) . Map.map negateDs
  varIsC (Vs1 _ _ C) = True
  varIsC (Vs2 _ _ C) = True
  varIsC _ = False
  negateDs m = m >>= cify where
    cify (Vs1 x1 x2 D) = Neg (Var $ Vs1 x1 x2 C)
    cify (Vs2 x1 x2 D) = Neg (Var $ Vs2 x1 x2 C)
    cify x = Var x

-------------------------------------------------------------------------------

actions :: [GameObject] -> [Action]
actions objects = [x | Execute x <- objects]

gameToSetting :: MonadError FileError m => Name -> [GameObject] -> m Setting
gameToSetting name = foldM addToSetting emptySetting where
  emptySetting = Setting name Map.empty Map.empty Map.empty
  addToSetting setting (Agent a) =
    (\x -> setting{agents=x}) <$> addToMap AgentT (defName a) a (agents setting)
  addToSetting setting (Theory t) =
    (\x -> setting{theories=x}) <$> addToMap TheoryT (defName t) t (theories setting)
  addToSetting setting (Problem p v vs) =
    (\x -> setting{problems=x}) <$>
      addToMap ProblemT (defName p) (p, v, vs) (problems setting)
  addToSetting setting (Execute _) = return setting
  addToMap :: MonadError FileError m =>
    DefType -> Name -> x -> Map Name x -> m (Map Name x)
  addToMap t n val m = do
    when (Map.member n m) (throwError $ NameCollision t n)
    return $ Map.insert n val m

gameParser :: Parser [GameObject]
gameParser = many P.ignoredLine *> (parser `sepEndBy` many P.ignoredLine) <* end where
  end = many (void (char '\t') <|> P.ignoredToken) *> eof -- Ugh.

-------------------------------------------------------------------------------

parseFile :: FilePath -> IO [GameObject]
parseFile path = runFile (parse gameParser path) path

compileFile :: FilePath -> IO Setting
compileFile path = run . gameToSetting path =<< parseFile path

playGame :: Name -> [GameObject] -> IO ()
playGame name game = do
  setting <- run $ gameToSetting name game
  putStrLn "Setting:"
  displayBlock' (Text.pack "  ") setting
  putStrLn "Loaded. Executing..."
  putStrLn ""
  mapM_ (executeAction setting) (actions game)

playFile :: FilePath -> IO ()
playFile path = parseFile path >>= playGame path

playGame' :: Name -> Setting -> [GameObject] -> IO ()
playGame' name base game = do
  putStrLn "Setting loaded from other files:"
  displayBlock' (Text.pack "  ") base
  local <- run $ gameToSetting name game
  putStrLn "Setting from this file:"
  displayBlock' (Text.pack "  ") local
  setting <- run $ mergeSettingsR base local
  putStrLn "Merged. Executing..."
  putStrLn ""
  mapM_ (executeAction setting) (actions game)

playFile' :: FilePath -> Setting -> IO ()
playFile' path setting = parseFile path >>= playGame' path setting
