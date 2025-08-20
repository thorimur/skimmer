import Lean
import Batteries

class Reflike (Ref : Type → Type) where
  new {α} : α → BaseIO (Ref α)
  get {α} : Ref α → BaseIO α
  set {α} : Ref α → α → BaseIO Unit
  modify {α} : Ref α → (α → α) → BaseIO Unit
  modifyGet {α} : Ref α → (α → β × α) → BaseIO β

-- attribute [inline] Reflike.new Reflike.get Reflike.set Reflike.modify Reflike.modifyGet

instance : Reflike IO.Ref where
  new := IO.mkRef
  get := (·.get)
  set := (·.set)
  modify := (·.modify)
  modifyGet := (·.modifyGet)

instance : Reflike Std.Mutex where
  new := Std.Mutex.new
  get m := m.atomically get
  set m a := m.atomically (·.set a)
  modify m f := m.atomically (modify f)
  modifyGet m f := m.atomically (modifyGet f)
