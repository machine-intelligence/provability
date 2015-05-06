module Display where
import Data.List (transpose)
import Data.Map hiding (map, foldr)
import qualified Data.Map as Map
import Text.Printf (printf)

type Table = [[String]]

padr :: a -> Int -> [a] -> [a]
padr x n xs = xs ++ replicate (n - length xs) x

padl :: a -> Int -> [a] -> [a]
padl x n xs = replicate (n - length xs) x ++ xs

listmapToTable :: (Show k, Ord k) => [k] -> Map k [String] -> Table
listmapToTable [] _ = []
listmapToTable ks m = header : rows where
  header = "" : "│" : map show ks
  unpaddedCols = map (m !) ks
  cols = map (padr "" $ maximum $ map length unpaddedCols) unpaddedCols
  rows = zipWith addNum [0 :: Int ..] (transpose cols)
  addNum n row = show n : "│" : row

mapToTable :: (Ord k, Show k, Show v) => Map k v -> Table
mapToTable = map (\(k, v) -> [show k, ": ", show v]) . toAscList

displayMap' :: (Ord k, Show k, Show v) => Int -> Map k v -> IO ()
displayMap' indent m = mapM_ (uncurry showLine) squaredLines where
	spaces = replicate indent ' '
	showLine label val = printf "%s%s : %s\n" spaces label (show val)
	squaredLines = [(padr ' ' maxwidth (show k), v) | (k, v) <- toAscList m]
	maxwidth = foldWithKey (\k v n -> max (length $ show k) n) 0 m

displayMap :: (Ord k, Show k, Show v) => Map k v -> IO ()
displayMap = displayMap' 0

squareUp' :: String -> String -> Table -> [[String]]
squareUp' l r rows = map normalizeRow paddedRows where
  paddedRows = map (padr "" $ maxlen rows) rows
  maxlen = foldr (max . length) 0
  normalizeRow = zipWith normalizeCell [0..] where
    normalizeCell i c = l ++ padr ' ' (colwidth i) c ++ r
  colwidth i = maximum [length $ row !! i | row <- paddedRows]

squareUp :: Table -> [[String]]
squareUp = squareUp' " " " "

renderTable :: Table -> String
renderTable table = unlines $ map concat (squareUp table)

displayTable :: Table -> IO ()
displayTable = putStrLn . renderTable
