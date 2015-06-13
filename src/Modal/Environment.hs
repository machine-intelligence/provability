{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Modal.Environment where
import Control.Monad (when)
import Data.Either (partitionEithers)
import Data.Map (Map)
import Data.Set (Set)
import Modal.Formulas (ModalFormula)
import Modal.Statement
import Modal.Utilities
import Text.Printf (printf)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

--------------------------------------------------------------------------------
-- The environment type. It holds all of the agents on a given side of combat.
-- Agents in an Env A O have action type A and consider opponents with option
-- type O. That is, these agents can return elements of A and face opponents
-- who can return elements of O.

type AgentMap v a o = Map a (ModalFormula (v a o))

newtype Env v a o = Env { _participants :: Map Name (AgentMap v a o, Int) }

instance Show a => Show (Env v a o) where
  show (Env ps) = printf "{%s}" (List.intercalate ", " $ Map.keys ps)

nobody :: Env v a o
nobody = Env Map.empty

missingSubagents :: AgentVar v => Env v a o -> AgentMap v a o-> Set Name
missingSubagents env agent = subagents agent Set.\\ namesIn env where
  namesIn = Set.fromList . Map.keys . _participants

participants :: Env v a o -> Map Name (AgentMap v a o)
participants = Map.map fst . _participants

-- The modal rank of each agent is tracked, but not yet used.
rankedParticipants :: Env v a o -> Map Name Int
rankedParticipants = Map.map snd . _participants

rankIn :: AgentVar v => Env v a o -> Name -> AgentMap v a o -> Either EnvError Int
rankIn env name agent = if null missings then Right rank else Left err where
  err = MissingSubagents name (Set.fromList missings)
  rank = if null ranks then 0 else succ $ maximum ranks
  (missings, ranks) = partitionEithers $ Set.toList $ Set.map lookupRank subs
  subs = subagents agent
  lookupRank n = maybe (Left n) (Right . snd) $ Map.lookup n (_participants env)

-------------------------------------------------------------------------------

-- If you want to deal with environments in a safe way, you need to handle
-- errors of this type.
data EnvError
  = UnknownPlayer Name
  | NameCollision Name
  | MissingSubagents Name (Set Name)
  deriving (Eq, Ord, Read)

instance Show EnvError where
  show (UnknownPlayer n) = printf "Player %s not found in the environment." n
  show (NameCollision n) = printf "%s is already in the environment!" n
  show (MissingSubagents n ns) = printf "Unknown agents referenced by %s: %s" n
    (List.intercalate ", " $ Set.toList ns)

-------------------------------------------------------------------------------
-- Functions that insert agents into environments.

-- This is the safe way of inserting an agent into an environment.
insert :: AgentVar v =>
  Env v a o -> Name -> AgentMap v a o -> Either EnvError (Env v a o)
insert env name agent = do
  (when $ Map.member name $ _participants env) (Left $ NameCollision name)
  rank <- rankIn env name agent
  return env{_participants=Map.insert name (agent, rank) (_participants env)}

insertAll :: AgentVar v =>
  Env v a o -> [(Name, AgentMap v a o)] -> Either EnvError (Env v a o)
insertAll env ((n, p):xs) = insert env n p >>= flip insertAll xs
insertAll env [] = Right env

-- A safe way to start building an environment.
-- Example: env = nobody @< cooperateBot @+ defectBot @+ fairBot
(@<) :: AgentVar v =>
  Env v a o -> (Name, AgentMap v a o) -> Either EnvError (Env v a o)
(@<) e = uncurry (insert e)

-- A safe combinator for continuing to build an environment
-- Example: env = nobody @< cooperateBot @+ defectBot @+ fairBot
(@+) :: AgentVar v =>
  Either EnvError (Env v a o) -> (Name, AgentMap v a o) -> Either EnvError (Env v a o)
e @+ nf = e >>= (@< nf)

-- An inline version of insertAll
(@++) :: AgentVar v =>
  Either EnvError (Env v a o) -> [(Name, AgentMap v a o)] -> Either EnvError (Env v a o)
e @++ nps = e >>= flip insertAll nps

-- The unsafe way of building environments
(@!) :: AgentVar v => Env v a o -> (Name, AgentMap v a o) -> Env v a o
(@!) e = uncurry (force .: insert e)
