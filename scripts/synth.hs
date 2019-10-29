#!/usr/bin/env stack
{- stack script
   --resolver lts-14.7
   --package shelly
   --package optparse-simple
   --package text
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

import           Shelly
import           Options.Applicative.Simple
import           Control.Applicative
import           Data.Monoid
import           Data.Maybe
import qualified Data.Text                     as T
default (T.Text)

main :: IO ()
main = do
    (file,()) <- simpleOptions
        "ver 2.0"
        "synth.hs"
        "Synthesise topEntity module."
        (optional $ argument str $ metavar "FILE" <> help "File to synhesise")
        empty

    shelly $ escaping False $ run_
        "stack exec -- clash"
        ["--verilog", "-isrc", "-outputdir build", fromMaybe "app/Main.hs" file]
