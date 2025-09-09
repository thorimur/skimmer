import Lean

-- We may need this to use a Reflike.
-- What about `Std.Mutex.atomicallyOnce`? Is that better?
-- We might want to use `CondVar`. Is that better than waiting on a promise?

def DynamicPromiseRef (α : Type) := IO.Ref (Option <| IO.Promise α × α)

def DynamicPromiseRef.modifyGetAndResolveIf (init : α) (f : α → α) (p : α → Bool) (ref : DynamicPromiseRef α) : BaseIO (IO.Promise α) := do
  let (pr, val) ← (← ref.get).getDM do
    haveI : Nonempty α := ⟨init⟩
    return (← IO.Promise.new, init)
  let val := f val
  if p val then
    pr.resolve val
  ref.set (some (pr, val))
  return pr

def DynamicPromiseRef.modifyGetAndResolveIfM {m} [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT BaseIO m] (init : α) (f : α → m α) (p : α → Bool) (ref : DynamicPromiseRef α) : m (IO.Promise α) := do
  let (pr, val) ← (← ref.get).getDM do
    haveI : Nonempty α := ⟨init⟩
    return (← IO.Promise.new, init)
  let val ← f val
  if p val then
    pr.resolve val
  ref.set (some (pr, val))
  return pr
