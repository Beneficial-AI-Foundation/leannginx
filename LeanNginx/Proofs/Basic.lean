import LeanNginx.Response

set_option linter.unusedSimpArgs false
/-! Supporting lemmas for `LeanNginx/Spec.lean`. -/
namespace LeanNginx.Proofs
open LeanNginx

/-! ## Path normalisation -/

theorem normSegs_safe : ∀ (l acc r : List Bytes), (∀ s ∈ acc, Safe s) →
    normSegs l acc = some r → ∀ s ∈ r, Safe s
  | [], acc, r, hacc, h => by
    simp [normSegs] at h; subst h; intro s hs; exact hacc s (List.mem_reverse.mp hs)
  | s :: rest, acc, r, hacc, h => by
    simp only [normSegs] at h
    by_cases h1 : (s.isEmpty || s == b!".") = true
    · simp only [h1, ↓reduceIte] at h; exact normSegs_safe rest acc r hacc h
    · simp only [h1, ↓reduceIte] at h
      by_cases h2 : (s == b!"..") = true
      · simp only [h2, ↓reduceIte] at h
        cases acc with
        | nil => simp at h
        | cons a acc' =>
          exact normSegs_safe rest acc' r (fun x hx => hacc x (List.mem_cons_of_mem _ hx)) h
      · simp only [h2, ↓reduceIte] at h
        by_cases h3 : segOk s = true
        · simp only [h3, ↓reduceIte] at h
          refine normSegs_safe rest (s :: acc) r ?_ h
          intro x hx
          cases List.mem_cons.mp hx with
          | inl e => subst e; exact h3
          | inr e => exact hacc x e
        · simp only [h3, ↓reduceIte] at h; simp at h

theorem normalizePath_safe (raw : Bytes) (np : NPath) (h : normalizePath raw = some np) :
    ∀ s ∈ np.segs, Safe s := by
  unfold normalizePath at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨d, _, segs, hs, rfl⟩ := h
    exact normSegs_safe _ [] segs (by simp) hs
  · simp at h

/-! ## Header fields -/

theorem tchar_lower_nat : ∀ n, n < 256 → isTChar n.toUInt8 = true → isTChar (toLower n.toUInt8) = true := by
  decide +kernel

theorem tchar_lower (c : UInt8) (h : isTChar c = true) : isTChar (toLower c) = true := by
  have := tchar_lower_nat c.toNat c.toNat_lt (by simpa using h)
  simpa using this

theorem isToken_lower (b : Bytes) (h : isToken b = true) : isToken (lowerB b) = true := by
  simp only [isToken, lowerB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, List.mem_map] at *
  refine ⟨by simpa using h.1, ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  exact tchar_lower c (h.2 c hc)

theorem parseField_ok (l : Bytes) (f : Bytes × Bytes) (h : parseField l = some f) :
    isToken f.1 = true ∧ validValue f.2 = true := by
  unfold parseField at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rename_i hc
      simp at h; subst h
      simp only [Bool.and_eq_true] at hc
      exact ⟨isToken_lower _ hc.1, hc.2⟩
    · simp at h

theorem parseFields_ok : ∀ (ls : List Bytes) (fs : List (Bytes × Bytes)), parseFields ls = some fs →
    ∀ f ∈ fs, isToken f.1 = true ∧ validValue f.2 = true
  | [], fs, h => by simp [parseFields] at h; subst h; simp
  | l :: ls, fs, h => by
    simp only [parseFields, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨f, hf, fs', hfs, rfl⟩ := h
    intro g hg
    cases List.mem_cons.mp hg with
    | inl e => subst e; exact parseField_ok l _ hf
    | inr e => exact parseFields_ok ls fs' hfs g e

theorem validValue_no_ctl (v : Bytes) (h : validValue v = true) :
    ∀ c ∈ v, c ≠ 0 ∧ c ≠ 10 ∧ c ≠ 13 := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simp [fieldByteOk] at this
  rcases this with h9 | ⟨h32, _⟩
  · subst h9; decide
  · refine ⟨?_, ?_, ?_⟩ <;> (intro e; subst e; revert h32; decide)

theorem parseVersion_le (v : Bytes) (n : Nat) (h : parseVersion v = .ok n) : n ≤ 1 := by
  unfold parseVersion at h
  split at h
  · split at h
    · cases h; decide
    · split at h
      · cases h; decide
      · split at h <;> cases h
  · cases h

/-- Everything an accepted request satisfies, in one place. -/
theorem parseRequest_ok (head : Bytes) (r : Request) (h : parseRequest head = .ok r) :
    isToken r.method = true ∧ r.minor ≤ 1 ∧
    (∃ ls, parseFields ls = some r.headers) ∧
    headerVals r.headers b!"transfer-encoding" = [] ∧
    parseContentLength r.headers = .ok r.contentLength ∧
    hostOk' r.host = true := by
  unfold parseRequest at h
  repeat' (first | split at h | (simp at h; done) | cases h)
  refine ⟨?_, parseVersion_le _ _ ‹_›, ⟨_, ‹_›⟩, ?_, ‹_›, ‹_›⟩ <;> simp_all

theorem parseContentLength_agree (hs : List (Bytes × Bytes)) (n : Nat)
    (h : parseContentLength hs = .ok n) :
    ∀ v ∈ headerVals hs b!"content-length", parseNat? v = some n := by
  unfold parseContentLength at h
  split at h
  · simp_all
  · rename_i v vs hv
    rw [hv]
    split at h
    · cases h
    · rename_i m hm
      split at h
      · rename_i hall
        cases h
        intro x hx
        cases List.mem_cons.mp hx with
        | inl e => subst e; exact hm
        | inr e =>
          have := List.all_eq_true.mp hall x e
          simp at this; subst this; exact hm
      · cases h

end LeanNginx.Proofs
