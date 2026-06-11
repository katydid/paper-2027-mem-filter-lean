-- Thunk.lean implements classes for Thunk.

instance [DecidableEq α] : DecidableEq (Thunk α) :=
  fun a b =>
    if hget: a.get = b.get
    then by
      apply Decidable.isTrue
      have h' := Thunk.ext hget
      assumption
    else by
      apply Decidable.isFalse
      intro heq
      apply hget
      rw [heq]

instance [Ord α]: Ord (Thunk α) where
  compare : Thunk α → Thunk α → Ordering :=
    fun a b =>
      compare a.get b.get

instance [Repr α]: Repr (Thunk α) where
  reprPrec a n := reprPrec a.get n

instance [Hashable α]: Hashable (Thunk α) where
  hash : Thunk α → UInt64 := fun a => hash a.get
