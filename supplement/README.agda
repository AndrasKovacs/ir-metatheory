{-# OPTIONS --without-K --rewriting #-}
-- rewriting is used only in CodeCircExample to axiomatize object-theoretic rules

module README where

-- This folder was checked using Agda 2.8.0 and standard library 2.2.
-- Tool installation instructions can be found here:
--   https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html

import Lib                   -- Standard definitions and re-exports.
import PlainIR               -- Postulated IR types, examples. Section 2.2 in paper.
import IndexedIR             -- Postulated IIR types, examples. Section 2.3 in paper.
import DeriveIndexed         -- Construction of IIR types from IR types, examples. Section 3 in paper.
import IRCanonicity          -- Logical predicate interpretation of IR types using IIR types, examples.
                             -- Sections 4.3.2 and 4.3.3 in paper.
import CodeCircExample       -- Extended example for deriving Agda-style rules for Codeᵒ from its IIR specification.
