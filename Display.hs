module Display where
import Data.Map hiding (map, foldr)

type Table = [[String]]

mapListToTable :: (Ord k, Enum k, Show k, Show v) => [k] -> [Map k v] -> Table
mapListToTable [] _    = []
mapListToTable ks maps = header : rows where
  header = "":"│":map show ks
  rows = [show n : "│" : map (show . (m !)) ks | (n, m) <- zip [0..] maps]

mapToTable :: (Ord k, Show k, Show v) => Map k v -> Table
mapToTable = map (\(k, v) -> [show k, " :  ", show v]) . toAscList

displayMap :: (Ord k, Show k, Show v) => Map k v -> IO ()
displayMap = displayTable . mapToTable

squareUp :: Table -> [[String]]
squareUp rows = map normalizeRow paddedRows where
  paddedRows = map (pad "" $ maxlen rows) rows
  pad x n xs = xs ++ replicate (n - length xs) x
  maxlen = foldr (max . length) 0
  normalizeRow row = zipWith normalizeCell [0..] row where
    normalizeCell i = pad ' ' (colwidth i)
  colwidth i = maximum [length $ r !! i | r <- paddedRows]

renderTable :: Table -> String
renderTable table = unlines $ map concat (squareUp table)

displayTable :: Table -> IO ()
displayTable = putStrLn . renderTable
