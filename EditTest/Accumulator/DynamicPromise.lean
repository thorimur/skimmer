import Lean

-- We may need this to use a Reflike.
-- What about `Std.Mutex.atomicallyOnce`? Is that better?
-- We might want to use `CondVar`. Is that better than waiting on a promise?

def DynamicPromiseRef (α β : Type) := IO.Ref (Option <| IO.Promise β × α)

def DynamicPromiseRef.modifyGetAndResolveIf [Nonempty β] (init : α) (f : α → α) (p : α → Bool) (fulfill : α → β)
    (ref : DynamicPromiseRef α β) : BaseIO (IO.Promise β) := do
  let (pr, val) ← (← ref.get).getDM do return (← IO.Promise.new, init)
  let val := f val
  if p val then
    pr.resolve <| fulfill val
  ref.set (some (pr, val))
  return pr

@[inline] def DynamicPromiseRef.modifyGetAndResolveIf' [Nonempty β]
    (init : α) (f : α → α) (p : α → Bool) (fulfill : α → β)
    (ref : DynamicPromiseRef α β) : BaseIO Unit :=
  discard <| ref.modifyGetAndResolveIf init f p fulfill

def DynamicPromiseRef.modifyGetAndResolveIfM {m} [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT BaseIO m]
    [Nonempty β] (init : α) (f : α → m α) (p : α → m Bool) (fulfill : α → m β) (ref : DynamicPromiseRef α β) :
    m (IO.Promise β) := do
  let (pr, val) ← (← ref.get).getDM do return (← IO.Promise.new, init)
  let val ← f val
  if ← p val then
    pr.resolve <|← fulfill val
  ref.set (some (pr, val))
  return pr
