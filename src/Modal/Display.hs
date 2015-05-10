{-# LANGUAGE OverloadedStrings #-}
module Modal.Display where
import Control.Arrow (first)
import Data.List (transpose)
import Data.Map hiding (map, foldr)
import qualified Data.Map as Map
import Data.Monoid ((<>), mconcat)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text.IO
import Modal.Utilities
import Text.Printf (printf)

type Table = [[String]]

padr :: a -> Int -> [a] -> [a]
padr x n xs = xs ++ replicate (n - length xs) x

padl :: a -> Int -> [a] -> [a]
padl x n xs = replicate (n - length xs) x ++ xs

listmapToTable :: (Show k, Ord k) => [k] -> Map k [String] -> Table
listmapToTable [] _ = []
listmapToTable ks m = header : rows where
  header = "" : " │" : map (printf " %s" . show) ks
  unpaddedCols = map (m !) ks
  cols = map (padr "" $ maximum $ map length unpaddedCols) unpaddedCols
  rows = zipWith addNum [0 :: Int ..] (transpose cols)
  addNum n row = show n : " │" : (map (printf " %s") row)

mapToTable :: (Ord k, Show k, Show v) => Map k v -> Table
mapToTable m = [row k v | (k, v) <- toAscList m] where
  row k v = [padr ' ' (maxwidth + 2) (printf "%s :  " (show k)), show v]
  maxwidth = foldWithKey (\k v n -> max (length $ show k) n) 0 m

displayMap :: (Ord k, Show k, Show v) => Map k v -> IO ()
displayMap = displayTable . mapToTable

squareUp' :: String -> String -> Table -> [[String]]
squareUp' l r rows = map normalizeRow paddedRows where
  paddedRows = map (padr "" $ maxlen rows) rows
  maxlen = foldr (max . length) 0
  normalizeRow = zipWith normalizeCell [0..] where
    normalizeCell i c = l ++ padr ' ' (colwidth i) c ++ r
  colwidth i = maximum [length $ row !! i | row <- paddedRows]

squareUp :: Table -> [[String]]
squareUp = squareUp' "" ""

renderTable :: Table -> String
renderTable table = unlines $ map concat (squareUp table)

indentTable :: String -> Table -> Table
indentTable indent = map (indent:)

displayTable :: Table -> IO ()
displayTable = putStrLn . renderTable

class Blockable a where
  blockLines :: a -> [(Int, Text)]

increaseIndent :: [(Int, Text)] -> [(Int, Text)]
increaseIndent = map (first succ)

renderBlock' :: Blockable a => Text -> a -> Text
renderBlock' indent = Text.unlines . map (uncurry indented) . blockLines where
  indented n = (mconcat (replicate n indent) <>)

renderBlock :: Blockable a => a -> Text
renderBlock = renderBlock' "  "

displayBlock' :: Blockable a => Text -> a -> IO ()
displayBlock' = Text.IO.putStrLn .: renderBlock'

displayBlock :: Blockable a => a -> IO ()
displayBlock = Text.IO.putStrLn . renderBlock
