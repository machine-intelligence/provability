module ModalEnvironment where
import Control.Applicative
import ModalFormulas
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text hiding (maximum)

type Name = Text

data AgentVar = Me | Them | ThemVs Name deriving (Eq, Ord)
instance Show AgentVar where
instance Read AgentVar where

data ModalAgent = ModalAgent
  { agentName :: Name
  , agentFormula :: ModalFormula AgentVar
  } deriving (Eq, Ord, Read)
instance Show ModalAgent where

newtype Environment = Environment { participants :: Map Name (Int, ModalAgent) }

nobody :: Environment
nobody = Environment Map.empty

references :: ModalAgent -> Set Name
references = Set.fromList . names . Set.toList . allVars . agentFormula where
  names xs = [name | ThemVs name <- xs]

insert :: Environment -> ModalAgent -> Maybe Environment
insert env agent = do
  level <- checkReferences env agent
  return $ Environment $ Map.insert (agentName agent) (level, agent) $ participants env

checkReferences :: Environment -> ModalAgent -> Maybe Int
checkReferences env agent = (1 +) . maximum <$> levels where
  levels = mapM lookupLevel (Set.toList $ references agent)
  lookupLevel name = fst <$> Map.lookup name (participants env)

infixr <^>
(<^>) :: ModalAgent -> Maybe Environment -> Maybe Environment
a <^> e = e >>= flip insert a

-- Example:
-- environment :: Maybe Environment
-- environment = fairBot <^> prudentBot <^> Just nobody
