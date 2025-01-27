module T417.Value where

import StrictList qualified as SL
import T417.Common

--------------------------------------------------------------------------------

data Value
  = VVar VarName Spine
  | VConst ConstName Spine ~Value
  | VType
  | VKind
  | VLam VarName VType (Value -> Value)
  | VPi VarName VType (Value -> VType)

data Spine
  = SNil
  | SConstApp (SL.List Value)
  | SApp Spine Value

type VType = Value
