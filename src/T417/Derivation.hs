module T417.Derivation where

import T417.Common
import T417.Syntax

--------------------------------------------------------------------------------

-- Δ; Γ ⊢ M : N
data Judgment = Judgment
  { defs :: Defs,
    ctx :: [(VarName, Type)],
    term :: Term,
    type_ :: Type
  }

-- verify :: Vector Rule -> Maybe (Vector Judgment)
-- verify = undefined
