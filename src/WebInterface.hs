{-# LANGUAGE CPP, TemplateHaskell, QuasiQuotes, ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types, DeriveDataTypeable #-}
module Main (
    main
) where

import Prelude hiding ((!!))
import Control.Applicative ((<$>))
import Control.Monad.Trans (liftIO)
import GHCJS.DOM
import GHCJS.DOM.CSSStyleDeclaration
import GHCJS.DOM.Document
import GHCJS.DOM.HTMLElement
import GHCJS.DOM.Element
import GHCJS.DOM.HTMLTextAreaElement
import GHCJS.DOM.Node
import GHCJS.DOM.EventM
import GHCJS.DOM.Types
import Data.Text.Lazy (Text, unpack)
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Text.Hamlet (shamlet)
import Text.Blaze.Html (Html)
import Text.Parsec hiding ((<|>), optional, many, State)
import qualified Data.Text as T (unpack, pack)

import Modal.Combat
import Modal.Utilities

runGame source = do
  game <- run $ parse gameParser "input" $ T.pack source
  playGame "game" $ game

main = runWebGUI $ \ webView -> do
  enableInspector webView
  Just doc <- webViewGetDomDocument webView
  Just body <- documentGetBody doc
  Just div <- fmap castToHTMLDivElement <$> documentCreateElement doc "div"
  mbTerminal <- fmap castToHTMLDivElement <$> documentGetElementById doc "terminal"
  case mbTerminal of
    Just terminal -> do
      Just style <- elementGetStyle terminal
      cssStyleDeclarationSetProperty style "height" "200px" ""
      cssStyleDeclarationSetProperty style "position" "absolute" ""
      cssStyleDeclarationSetProperty style "bottom" "0" ""
      nodeInsertBefore body (Just div) (Just terminal)
    _             -> do
      nodeAppendChild body (Just div)
  Just input <- fmap castToHTMLTextAreaElement <$> documentGetElementById doc "input"
  Just btn <- fmap castToHTMLInputElement      <$> documentGetElementById doc "btn"
  Just output <- fmap castToHTMLPreElement     <$> documentGetElementById doc "output"
  elementOnclick btn $ liftIO $ do
    source <- htmlTextAreaElementGetValue input
    htmlElementSetInnerHTML output ""
    runGame $ unpack source
  return ()
