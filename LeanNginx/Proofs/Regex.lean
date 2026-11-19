import LeanNginx.Regex
/-! The derivative matcher decides `Matches` exactly. -/

set_option linter.unusedSimpArgs false

namespace LeanNginx.Proofs
open LeanNginx

/-! ## Inversion lemmas -/

theorem none_inv {w : Bytes} (h : Matches .none w) : False := by cases h

theorem eps_inv {w : Bytes} (h : Matches .eps w) : w = [] := by cases h; rfl

theorem cls_inv {c : CClass} {w : Bytes} (h : Matches (.cls c) w) :
    ∃ x, w = [x] ∧ c.mem x = true := by
  cases h with
  | cls hm => exact ⟨_, rfl, hm⟩

theorem seq_inv {a b : Re} {w : Bytes} (h : Matches (.seq a b) w) :
    ∃ s t, w = s ++ t ∧ Matches a s ∧ Matches b t := by
  cases h with
  | seq ha hb => exact ⟨_, _, rfl, ha, hb⟩

theorem alt_inv {a b : Re} {w : Bytes} (h : Matches (.alt a b) w) : Matches a w ∨ Matches b w := by
  cases h with
  | altL h => exact Or.inl h
  | altR h => exact Or.inr h

/-- A non-empty word matched by `a*` starts with a non-empty piece matched by `a`. -/
theorem star_cons_inv {a : Re} {w : Bytes} (h : Matches (.star a) w) :
    ∀ x s, w = x :: s → ∃ s1 t, s = s1 ++ t ∧ Matches a (x :: s1) ∧ Matches (.star a) t := by
  generalize hr : Re.star a = r at h
  induction h with
  | eps => cases hr
  | cls _ => cases hr
  | seq _ _ _ _ => cases hr
  | altL _ _ => cases hr
  | altR _ _ => cases hr
  | starNil => intro x s hw; cases hw
  | @starCons a' s' t' h1 h2 _ ih2 =>
    cases hr
    intro x s hw
    cases s' with
    | nil => exact ih2 rfl x s hw
    | cons y s'' =>
      simp only [List.cons_append, List.cons.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨s'', t', rfl, h1, h2⟩

/-! ## Smart constructors preserve the language -/

theorem mkSeq_iff (a b : Re) (w : Bytes) : Matches (mkSeq a b) w ↔ Matches (.seq a b) w := by
  unfold mkSeq
  split
  · constructor
    · intro h; exact (none_inv h).elim
    · intro h; obtain ⟨s, t, _, ha, _⟩ := seq_inv h; exact (none_inv ha).elim
  · constructor
    · intro h; exact (none_inv h).elim
    · intro h; obtain ⟨s, t, _, _, hb⟩ := seq_inv h; exact (none_inv hb).elim
  · constructor
    · intro h; have := Matches.seq Matches.eps h; simpa using this
    · intro h
      obtain ⟨s, t, rfl, ha, hb⟩ := seq_inv h
      rw [eps_inv ha]; simpa using hb
  · exact Iff.rfl

theorem mkAlt_iff (a b : Re) (w : Bytes) : Matches (mkAlt a b) w ↔ Matches (.alt a b) w := by
  unfold mkAlt
  split
  · constructor
    · intro h; exact Matches.altR h
    · intro h; rcases alt_inv h with h | h
      · exact (none_inv h).elim
      · exact h
  · constructor
    · intro h; exact Matches.altL h
    · intro h; rcases alt_inv h with h | h
      · exact h
      · exact (none_inv h).elim
  · split
    · rename_i heq
      subst heq
      constructor
      · intro h; exact Matches.altL h
      · intro h; rcases alt_inv h with h | h <;> exact h
    · exact Iff.rfl

/-! ## Nullability and derivatives -/

theorem nullable_iff : ∀ r : Re, r.nullable = true ↔ Matches r []
  | .none => by simp [Re.nullable]; intro h; exact none_inv h
  | .eps => by simp [Re.nullable]; exact Matches.eps
  | .cls c => by
    simp only [Re.nullable, Bool.false_eq_true, false_iff]
    intro h; obtain ⟨x, hx, _⟩ := cls_inv h; cases hx
  | .seq a b => by
    simp only [Re.nullable, Bool.and_eq_true]
    rw [nullable_iff a, nullable_iff b]
    constructor
    · rintro ⟨ha, hb⟩; have := Matches.seq ha hb; simpa using this
    · intro h
      obtain ⟨s, t, hw, ha, hb⟩ := seq_inv h
      have hs : s = [] := (List.append_eq_nil_iff.mp hw.symm).1
      have ht : t = [] := (List.append_eq_nil_iff.mp hw.symm).2
      subst hs; subst ht; exact ⟨ha, hb⟩
  | .alt a b => by
    simp only [Re.nullable, Bool.or_eq_true]
    rw [nullable_iff a, nullable_iff b]
    constructor
    · rintro (h | h)
      · exact Matches.altL h
      · exact Matches.altR h
    · intro h; exact alt_inv h
  | .star a => by simp [Re.nullable]; exact Matches.starNil

theorem deriv_iff : ∀ (r : Re) (x : UInt8) (s : Bytes), Matches (r.deriv x) s ↔ Matches r (x :: s)
  | .none, x, s => by
    simp only [Re.deriv]
    exact ⟨fun h => (none_inv h).elim, fun h => (none_inv h).elim⟩
  | .eps, x, s => by
    simp only [Re.deriv]
    exact ⟨fun h => (none_inv h).elim, fun h => by cases eps_inv h⟩
  | .cls c, x, s => by
    simp only [Re.deriv]
    split
    · rename_i hm
      constructor
      · intro h; rw [eps_inv h]; exact Matches.cls hm
      · intro h
        obtain ⟨y, hy, _⟩ := cls_inv h
        simp only [List.cons.injEq] at hy
        rw [hy.2]; exact Matches.eps
    · rename_i hm
      constructor
      · intro h; exact (none_inv h).elim
      · intro h
        obtain ⟨y, hy, hmy⟩ := cls_inv h
        simp only [List.cons.injEq] at hy
        rw [hy.1] at hm; exact absurd hmy hm
  | .seq a b, x, s => by
    have iha := deriv_iff a x
    have ihb := deriv_iff b x
    simp only [Re.deriv]
    split
    · rename_i hn
      rw [mkAlt_iff]
      constructor
      · intro h
        rcases alt_inv h with h | h
        · rw [mkSeq_iff] at h
          obtain ⟨s1, t, rfl, h1, h2⟩ := seq_inv h
          have := Matches.seq ((iha s1).mp h1) h2
          simpa using this
        · have := Matches.seq ((nullable_iff a).mp hn) ((ihb s).mp h)
          simpa using this
      · intro h
        obtain ⟨s1, t, hw, h1, h2⟩ := seq_inv h
        cases s1 with
        | nil =>
          simp only [List.nil_append] at hw
          subst hw
          exact Matches.altR ((ihb s).mpr h2)
        | cons y s1' =>
          simp only [List.cons_append, List.cons.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          refine Matches.altL ((mkSeq_iff _ _ _).mpr ?_)
          exact Matches.seq ((iha s1').mpr h1) h2
    · rename_i hn
      rw [mkSeq_iff]
      constructor
      · intro h
        obtain ⟨s1, t, rfl, h1, h2⟩ := seq_inv h
        have := Matches.seq ((iha s1).mp h1) h2
        simpa using this
      · intro h
        obtain ⟨s1, t, hw, h1, h2⟩ := seq_inv h
        cases s1 with
        | nil => exact absurd ((nullable_iff a).mpr h1) hn
        | cons y s1' =>
          simp only [List.cons_append, List.cons.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          exact Matches.seq ((iha s1').mpr h1) h2
  | .alt a b, x, s => by
    have iha := deriv_iff a x s
    have ihb := deriv_iff b x s
    simp only [Re.deriv]
    rw [mkAlt_iff]
    constructor
    · intro h
      rcases alt_inv h with h | h
      · exact Matches.altL (iha.mp h)
      · exact Matches.altR (ihb.mp h)
    · intro h
      rcases alt_inv h with h | h
      · exact Matches.altL (iha.mpr h)
      · exact Matches.altR (ihb.mpr h)
  | .star a, x, s => by
    have iha := deriv_iff a x
    simp only [Re.deriv]
    rw [mkSeq_iff]
    constructor
    · intro h
      obtain ⟨s1, t, rfl, h1, h2⟩ := seq_inv h
      have := Matches.starCons ((iha s1).mp h1) h2
      simpa using this
    · intro h
      obtain ⟨s1, t, rfl, h1, h2⟩ := star_cons_inv h x s rfl
      exact Matches.seq ((iha s1).mpr h1) h2

/-- **The matcher is exact**: `matchB r s` is true iff `s` is in the language of `r`. -/
theorem matchB_iff : ∀ (r : Re) (s : Bytes), r.matchB s = true ↔ Matches r s
  | r, [] => by simp only [Re.matchB]; exact nullable_iff r
  | r, x :: s => by
    simp only [Re.matchB]
    rw [matchB_iff (r.deriv x) s]
    exact deriv_iff r x s

end LeanNginx.Proofs
