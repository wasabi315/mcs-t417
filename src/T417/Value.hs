module T417.Value where

import T417.Common

--------------------------------------------------------------------------------

newtype Lvl = Lvl Int
  deriving newtype (Eq, Ord, Show, Num)

data Value
  = VVar Lvl Spine
  | VConst ConstName Spine ~Value
  | VType
  | VKind
  | VLam VarName VType (Value -> Value)
  | VPi VarName VType (Value -> VType)

data Spine
  = SNil
  | SConstApp [Value]
  | SApp Spine Value

type VType = Value
