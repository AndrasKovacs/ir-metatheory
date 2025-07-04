
module README where

import Lib                   -- standard definitions and re-exports
import UIP                   -- UIP separately from the without-K Lib
import PlainIR               -- postulated IR types
import IndexedIR             -- postulated IIR types
import DeriveIndexed         -- construction of IIR types from IR types
import DeriveIndexedExamples -- examples for constructed IIR types
import IRCanonicity          -- logical predicate interpretation of IR types using IIR types
