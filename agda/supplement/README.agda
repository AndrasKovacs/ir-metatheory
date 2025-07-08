
module README where

-- This folder was checked using Agda 2.8.0 and standard library 2.2.

import Lib                   -- Standard definitions and re-exports.
import UIP                   -- UIP, separately from Lib.
import PlainIR               -- Postulated IR types. Section 2.2 in paper.
import IndexedIR             -- Postulated IIR types. Section 2.3 in paper.
import DeriveIndexed         -- Construction of IIR types from IR types. Section 3 in paper.
import DeriveIndexedExamples -- Examples for constructed IIR types. Section 3.3 in paper.
import IRCanonicity          -- Logical predicate interpretation of IR types using IIR types. Sections 4.3.2 and 4.3.3 in paper.
