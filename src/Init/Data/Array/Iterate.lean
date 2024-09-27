prelude

import Init.Data.Fin
-- import Init.Data.Range

universe u v

namespace Array

structure IndexIterator (n : Nat) where
  val : Option (Fin n)
  step : Nat := 1

@[inline] protected def forInIndex {β : Type u} {n : Nat} {m : Type u → Type v} [Monad m] (iter : IndexIterator n) (init : β) (f : Fin n → β → m (ForInStep β)) : m β :=
  -- pass `stop` and `step` separately so the `range` object can be eliminated through inlining
  let rec @[specialize] loop (fuel step : Nat) (i : Fin n) (b : β) (h: i < n): m β := do
    match fuel with
     | 0   => pure b
     | fuel+1 => match (← f i b) with
        | ForInStep.done b  => pure b
        | ForInStep.yield b => do
            let i' := i + step
            if h': i' < n then
              loop fuel step (Fin.mk i' h') b h'
            else
              pure b

  match iter.val with
    | .none => pure init
    | .some fin =>
      if h: fin < n then
        loop n iter.step fin init h
      else
        pure init

instance {n: Nat}: ForIn m (IndexIterator n) (Fin n) where
  forIn := Array.forInIndex

-- Ideas: Implement start/end/step indices
def indices {α : Type u} (a : Array α) : IndexIterator a.size :=
  if h: a.size > 0 then
    { val := (Fin.mk 0 h) }
  else
    { val := none }

end Array
