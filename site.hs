{-# LANGUAGE OverloadedStrings #-}
module Main where

import Data.Monoid
import Hakyll
import Skylighting
import System.Exit
import Text.Pandoc.Options



main :: IO ()
main = do
  let
    myCompiler :: Compiler (Item String)
    myCompiler = pandocCompilerWith readerOpts writerOpts
      where
        readerOpts = defaultHakyllReaderOptions

        writerOpts = defaultHakyllWriterOptions
          { writerHTMLMathMethod = MathJax ""
          , writerExtensions = mconcat
            [ writerExtensions defaultHakyllWriterOptions
            , extensionsFromList
              [ Ext_tex_math_dollars
              , Ext_tex_math_double_backslash
              , Ext_latex_macros
              , Ext_fenced_code_blocks
              , Ext_fenced_code_attributes
              ]
            ]
          }

  hakyll $ do
    match "images/*" $ do
      route   idRoute
      compile copyFileCompiler

    match "css/*" $ do
      route   idRoute
      compile compressCssCompiler

    match (fromList ["index.md","about.md"]) $ do
      route   $ setExtension "html"
      compile $ myCompiler
        >>= loadAndApplyTemplate "templates/latex.html" defaultContext
        >>= loadAndApplyTemplate "templates/default.html" defaultContext
        >>= relativizeUrls

    match "src/**" $ do
      route $ setExtension "html"
      compile $ myCompiler
        >>= loadAndApplyTemplate "templates/latex.html" defaultContext
        >>= loadAndApplyTemplate "templates/default.html" defaultContext
        >>= relativizeUrls

    match "templates/*" $ compile templateBodyCompiler
