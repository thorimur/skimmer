/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean

namespace ST

variable {σ : Type} {m : Type → Type} [Monad m] [MonadLiftT (ST σ) m]

namespace Prim

@[inline] unsafe def Ref.modifyMUnsafe {α : Type} (r : Ref σ α) (f : α → m α) : m Unit := do
  let v ← Ref.take r
  let v ← f v
  Ref.set r v

@[inline] unsafe def Ref.modifyGetMUnsafe {α β : Type} (r : Ref σ α) (f : α → m (β × α)) : m β := do
  let v ← Ref.take r
  let (b, a) ← f v
  Ref.set r a
  pure b

@[implemented_by Ref.modifyMUnsafe]
def Ref.modifyM {α : Type} (r : Ref σ α) (f : α → m α) : m Unit := do
  let v ← Ref.get r
  let v ← f v
  Ref.set r v

@[implemented_by Ref.modifyGetMUnsafe]
def Ref.modifyGetM {α β : Type} (r : Ref σ α) (f : α → m (β × α)) : m β := do
  let v ← Ref.get r
  let (b, a) ← f v
  Ref.set r a
  pure b

end Prim

@[inline] def Ref.modifyM {α : Type} (r : Ref σ α) (f : α → m α) : m Unit :=
  liftM <| Prim.Ref.modifyM r f
/--
Atomically modifies a mutable reference cell by replacing its contents with the result of a function
call that simultaneously computes a value to return.
-/
@[inline] def Ref.modifyGetM {α : Type} {β : Type} (r : Ref σ α) (f : α → m (β × α)) : m β :=
  liftM <| Prim.Ref.modifyGetM r f
