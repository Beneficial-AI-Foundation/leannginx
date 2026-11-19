import LeanNginx.Proofs.Route
/-! Lemmas for encoding, escaping, header rendering, ranges, and selection. -/

set_option linter.unusedSimpArgs false

namespace LeanNginx.Proofs
open LeanNginx

/-! ## Percent-encoding -/

theorem hexVal_hexUpper : ∀ n, n < 16 → hexVal? (hexUpper n) = some n := by decide +kernel

theorem pathSafe_ne_pct_nat : ∀ n, n < 256 → pathSafeByte n.toUInt8 = true → n ≠ 37 := by
  decide +kernel

theorem pathSafe_ne_pct (c : UInt8) (h : pathSafeByte c = true) : c ≠ 37 := by
  intro e
  have := pathSafe_ne_pct_nat c.toNat c.toNat_lt (by simpa using h)
  subst e; exact this rfl

theorem percentDecode_cons (c : UInt8) (rest : Bytes) (hc : c ≠ 37) :
    percentDecode (c :: rest) = (c :: ·) <$> percentDecode rest := by
  rw [percentDecode.eq_def]
  split
  · simp at *
  · rename_i heq; cases heq; exact absurd rfl hc
  · rename_i heq; cases heq; exact absurd rfl hc
  · rename_i heq; cases heq; rfl

theorem percentDecode_percentEncode : ∀ b, percentDecode (percentEncode b) = some b
  | [] => rfl
  | c :: rest => by
    have ih := percentDecode_percentEncode rest
    unfold percentEncode
    split
    · rename_i hs
      rw [percentDecode_cons _ _ (pathSafe_ne_pct c hs), ih]; rfl
    · have h1 : c.toNat / 16 < 16 := by have := c.toNat_lt; omega
      have h2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
      simp only [percentDecode, bind, Option.bind, hexVal_hexUpper _ h1, hexVal_hexUpper _ h2, ih, pure]
      congr
      have : c.toNat / 16 * 16 + c.toNat % 16 = c.toNat := by omega
      rw [this]; simp

theorem percentEncode_byte_ok : ∀ b, ∀ c ∈ percentEncode b, pathSafeByte c = true ∨ c = 37 ∨ isAlpha c ∨ isDigit c
  | [] => by simp [percentEncode]
  | c :: rest => by
    have ih := percentEncode_byte_ok rest
    unfold percentEncode
    split
    · rename_i hs
      intro x hx
      cases List.mem_cons.mp hx with
      | inl e => subst e; exact Or.inl hs
      | inr e => exact ih x e
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with e | e | e | e
      · exact Or.inr (Or.inl e)
      · subst e; have := hexUpper_ok (c.toNat / 16) (by have := c.toNat_lt; omega); exact Or.inr (Or.inr this)
      · subst e; exact Or.inr (Or.inr (hexUpper_ok _ (Nat.mod_lt _ (by decide))))
      · exact ih x e
where
  hexUpper_ok : ∀ n, n < 16 → isAlpha (hexUpper n) = true ∨ isDigit (hexUpper n) = true := by
    decide +kernel

/-! ## HTML escaping -/

theorem htmlEscape_safe : ∀ b, ∀ c ∈ htmlEscape b, c ≠ 60 ∧ c ≠ 62 ∧ c ≠ 34
  | [] => by simp [htmlEscape]
  | c :: rest => by
    have ih := htmlEscape_safe rest
    intro x hx
    simp only [htmlEscape, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · revert x; decide
      · split at hx
        · revert x; decide
        · split at hx
          · revert x; decide
          · split at hx
            · revert x; decide
            · simp at hx; subst hx
              simp_all [beq_iff_eq]
    · exact ih x hx

/-! ## Header rendering -/

theorem fieldByteOk_nat : ∀ n, n < 256 → fieldByteOk n.toUInt8 = true → n ≠ 0 ∧ n ≠ 10 ∧ n ≠ 13 := by
  decide +kernel

theorem cleanValue_safe (v : Bytes) : ∀ c ∈ cleanValue v, c ≠ 0 ∧ c ≠ 10 ∧ c ≠ 13 := by
  intro c hc
  simp only [cleanValue, List.mem_filter] at hc
  have := fieldByteOk_nat c.toNat c.toNat_lt (by simpa using hc.2)
  refine ⟨?_, ?_, ?_⟩ <;> intro e <;> subst e <;> simp at this

theorem tchar_nat : ∀ n, n < 256 → isTChar n.toUInt8 = true →
    n ≠ 0 ∧ n ≠ 10 ∧ n ≠ 13 ∧ n ≠ 32 ∧ n ≠ 58 := by
  decide +kernel

theorem cleanName_safe (n : Bytes) : ∀ c ∈ cleanName n, c ≠ 0 ∧ c ≠ 10 ∧ c ≠ 13 ∧ c ≠ 32 ∧ c ≠ 58 := by
  intro c hc
  simp only [cleanName, List.mem_filter] at hc
  have := tchar_nat c.toNat c.toNat_lt (by simpa using hc.2)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> simp at this

/-! ## Ranges -/

theorem resolveRange_bounds (size : Nat) (spec : Bytes) (a b : Nat)
    (h : resolveRange size spec = .part a b) : a ≤ b ∧ b < size := by
  unfold resolveRange at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · split at h
            · cases h
            · rename_i hz; cases h
              simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hz
              omega
          · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · rename_i hlt
              split at h
              · cases h; omega
              · split at h
                · split at h
                  · cases h
                  · cases h; omega
                · cases h
      · cases h

/-! ## Host bytes -/

theorem hostByteOk_nat : ∀ n, n < 256 → hostByteOk n.toUInt8 = true →
    n ≠ 0 ∧ n ≠ 10 ∧ n ≠ 13 ∧ n ≠ 32 ∧ n ≠ 47 ∧ n ≠ 34 ∧ n ≠ 60 := by
  decide +kernel

end LeanNginx.Proofs
