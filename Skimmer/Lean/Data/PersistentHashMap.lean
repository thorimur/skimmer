/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean

#check Subtype

namespace Lean.PersistentHashMap

abbrev ArrayPair α β := Subtype fun ((keys, vals) : Array α × Array β) => keys.size = vals.size

@[inline] private def eraseBothIdx {α β} : (kv : ArrayPair α β) → Fin kv.val.1.size →
    ArrayPair α β
  | ⟨(keys, vals), heq⟩, idx =>
    let keys' := keys.eraseIdx idx
    let vals' := vals.eraseIdx (Eq.ndrec idx heq)
    have : keys.size - 1 = vals.size - 1 := by rw [heq]
    ⟨(keys',vals'), by simp only [Array.size_eraseIdx, keys', vals']; exact this⟩

partial def filterAux [BEq α] : Node α β → USize → (p : α → β → Bool) → Node α β
  | n@(Node.collision keys vals heq), _, p => Id.run do
    let initSize := keys.size
    let mut kv : ArrayPair α β := ⟨(keys,vals), heq⟩
    for h : i in 1...=initSize do
      -- argh, we must also prove that i is still less than the resulting size...
      let
  | n@(Node.entries entries), h, k =>
    let j       := (mod2Shift h shift).toNat
    let entry   := entries[j]!
    match entry with
    | Entry.null       => n
    | Entry.entry k' _ =>
      if k == k' then Node.entries (entries.set! j Entry.null) else n
    | Entry.ref node   =>
      let entries := entries.set! j Entry.null
      let newNode := eraseAux node (div2Shift h shift) k
      match isUnaryNode newNode with
      | none        => Node.entries (entries.set! j (Entry.ref newNode))
      | some (k, v) => Node.entries (entries.set! j (Entry.entry k v))

def erase {_ : BEq α} {_ : Hashable α} : PersistentHashMap α β → α → PersistentHashMap α β
  | { root }, k =>
    let h := hash k |>.toUSize
    { root := eraseAux root h k }
