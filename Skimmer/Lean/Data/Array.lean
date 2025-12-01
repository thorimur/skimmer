/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean

@[expose] public section

namespace Array


-- Patterned after `modifyMUnsafe`.
@[inline]
unsafe def modifyGetMUnsafe [Monad m] [Inhabited β] (xs : Array α) (i : Nat)
    (f : α → m (β × α)) : m (β × Array α) := do
  if h : i < xs.size then
    let v                := xs[i]
    -- Replace a[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
    -- Note: we assume that arrays have a uniform representation irrespective
    -- of the element type, and that it is valid to store `box(0)` in any array.
    let xs'               := xs.set i (unsafeCast ())
    let (b, v) ← f v
    pure (b, xs'.set i v (Nat.lt_of_lt_of_eq h (size_set ..).symm))
  else
    pure (default, xs)

@[implemented_by modifyGetMUnsafe]
def modifyGetM [Monad m] [Inhabited β] (xs : Array α) (i : Nat) (f : α → m (β × α)) :
    m (β × Array α) := do
  if h : i < xs.size then
    let v   := xs[i]
    let (b, v) ← f v
    pure (b, xs.set i v)
  else
    pure (default, xs)

@[inline]
def modifyGet [Inhabited β] (xs : Array α) (i : Nat) (f : α → β × α) : β × Array α :=
  Id.run <| modifyGetM xs i (pure <| f ·)
