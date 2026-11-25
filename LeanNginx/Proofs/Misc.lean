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

theorem proxySafe_ne_pct_nat : ∀ n, n < 256 → proxySafeByte n.toUInt8 = true → n ≠ 37 := by
  decide +kernel

theorem proxySafe_ne_pct (c : UInt8) (h : proxySafeByte c = true) : c ≠ 37 := by
  intro e
  have := proxySafe_ne_pct_nat c.toNat c.toNat_lt (by simpa using h)
  subst e; exact this rfl

theorem percentDecode_percentEncodeStrict : ∀ b, percentDecode (percentEncodeStrict b) = some b
  | [] => rfl
  | c :: rest => by
    have ih := percentDecode_percentEncodeStrict rest
    unfold percentEncodeStrict
    split
    · rename_i hs
      rw [percentDecode_cons _ _ (proxySafe_ne_pct c hs), ih]; rfl
    · have h1 : c.toNat / 16 < 16 := by have := c.toNat_lt; omega
      have h2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
      simp only [percentDecode, bind, Option.bind, hexVal_hexUpper _ h1, hexVal_hexUpper _ h2, ih, pure]
      congr
      have : c.toNat / 16 * 16 + c.toNat % 16 = c.toNat := by omega
      rw [this]; simp

theorem hexUpper_proxySafe : ∀ n, n < 16 → proxySafeByte (hexUpper n) = true := by decide +kernel

theorem percentEncodeStrict_bytes : ∀ b, ∀ c ∈ percentEncodeStrict b, proxySafeByte c = true ∨ c = 37
  | [] => by simp [percentEncodeStrict]
  | c :: rest => by
    have ih := percentEncodeStrict_bytes rest
    unfold percentEncodeStrict
    split
    · rename_i hs
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl hs
      · exact ih x hx
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | hx
      · exact Or.inr rfl
      · exact Or.inl (hexUpper_proxySafe _ (by have := c.toNat_lt; omega))
      · exact Or.inl (hexUpper_proxySafe _ (Nat.mod_lt _ (by decide)))
      · exact ih x hx

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


/-! ## Header framing: line counts -/

theorem decDigits_go_digits : ∀ fuel n (acc : Bytes), ∀ c ∈ decDigits.go fuel n acc, c ∈ acc ∨ isDigit c = true
  | 0, n, acc => by intro c hc; exact Or.inl hc
  | fuel + 1, n, acc => by
    intro c hc
    have hd : isDigit (48 + n % 10).toUInt8 = true := by
      have : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have key : ∀ m, m < 10 → isDigit (48 + m).toUInt8 = true := by decide +kernel
      exact key _ this
    simp only [decDigits.go] at hc
    split at hc
    · rcases List.mem_cons.mp hc with rfl | h
      · exact Or.inr hd
      · exact Or.inl h
    · rcases decDigits_go_digits fuel (n / 10) _ c hc with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr hd
        · exact Or.inl h
      · exact Or.inr h

theorem decDigits_no_lf (n : Nat) : (decDigits n).count 10 = 0 := by
  apply List.count_eq_zero.mpr
  intro hm
  rcases decDigits_go_digits _ n [] 10 hm with h | h
  · simp at h
  · exact absurd h (by decide)

theorem reason_no_lf (code : Nat) : (reason code).count 10 = 0 := by
  unfold reason; split <;> decide

theorem count_lf_of_safe (l : Bytes) (h : ∀ c ∈ l, c ≠ 10) : l.count 10 = 0 :=
  List.count_eq_zero.mpr (fun hm => h 10 hm rfl)

theorem statusLine_lf (code : Nat) : (statusLine code).count 10 = 1 := by
  unfold statusLine
  simp only [List.count_append, decDigits_no_lf]
  have hr : ((32 :: reason code) : Bytes).count 10 = 0 := by
    simp [List.count_cons, reason_no_lf]
  rw [hr]; decide

theorem renderField_lf (f : Bytes × Bytes) : (renderField f).count 10 = 1 := by
  unfold renderField
  simp only [List.count_append]
  rw [count_lf_of_safe _ (fun c hc => (cleanName_safe f.1 c hc).2.1),
      count_lf_of_safe _ (fun c hc => (cleanValue_safe f.2 c hc).2.1)]
  decide

theorem flatMap_renderField_lf : ∀ hs : List (Bytes × Bytes), (hs.flatMap renderField).count 10 = hs.length
  | [] => rfl
  | f :: hs => by
    simp only [List.flatMap_cons, List.count_append, renderField_lf, flatMap_renderField_lf hs,
      List.length_cons]
    omega


/-! ## Where a request head ends -/

theorem headEndAt_bound (b : ByteArray) (i e : Nat) (h : headEndAt b i = some e) :
    i < e ∧ e ≤ b.size := by
  unfold headEndAt at h
  split at h
  · split at h
    · rename_i h1; simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      cases h; omega
    · split at h
      · rename_i _ h2; simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        cases h; omega
      · cases h
  · cases h

theorem findHeadEndFrom_first (b : ByteArray) :
    ∀ k i, b.size - i = k → ∀ hl e, findHeadEndFrom b i = some (hl, e) →
      i ≤ hl ∧ hl < b.size ∧ headEndAt b hl = some e ∧ ∀ j, i ≤ j → j < hl → headEndAt b j = none := by
  intro k
  induction k with
  | zero =>
    intro i hk hl e h
    rw [findHeadEndFrom] at h
    split at h
    · omega
    · cases h
  | succ k ih =>
    intro i hk hl e h
    rw [findHeadEndFrom] at h
    split at h
    · rename_i hi
      split at h
      · rename_i e' he
        cases h
        exact ⟨Nat.le_refl _, hi, he, fun j h1 h2 => absurd h2 (by omega)⟩
      · rename_i he
        obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) (by omega) hl e h
        refine ⟨by omega, h2, h3, fun j hj1 hj2 => ?_⟩
        rcases Nat.eq_or_lt_of_le hj1 with rfl | hj
        · exact he
        · exact h4 j (by omega) hj2
    · cases h


/-! ## `splitFirst`, hosts, credentials -/

theorem splitFirst_fst_sub (sep : UInt8) : ∀ b, ∀ c ∈ (splitFirst sep b).1, c ∈ b
  | [] => by simp [splitFirst]
  | x :: rest => by
    intro c hc
    simp only [splitFirst] at hc
    split at hc
    · simp at hc
    · rcases List.mem_cons.mp hc with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (splitFirst_fst_sub sep rest c h)

theorem splitFirst_fst_no_sep (sep : UInt8) : ∀ b, sep ∉ (splitFirst sep b).1
  | [] => by simp [splitFirst]
  | x :: rest => by
    simp only [splitFirst]
    split
    · simp
    · rename_i hx
      intro hm
      rcases List.mem_cons.mp hm with rfl | h
      · simp at hx
      · exact splitFirst_fst_no_sep sep rest h

theorem toLower_hostByteOk_nat : ∀ n, n < 256 → hostByteOk n.toUInt8 = true → hostByteOk (toLower n.toUInt8) = true := by
  decide +kernel

theorem lowerB_hostByteOk (h : Bytes) (hh : ∀ c ∈ h, hostByteOk c = true) : ∀ c ∈ lowerB h, hostByteOk c = true := by
  intro c hc
  simp only [lowerB, List.mem_map] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  have := toLower_hostByteOk_nat x.toNat x.toNat_lt (by simpa using hh x hx)
  simpa using this


/-! ## Safe segments, rooted URIs, suffix matching -/

/-- A `Safe` segment is non-empty and contains no `/`. -/
theorem safe_props (seg : Bytes) (h : Safe seg) : seg ≠ [] ∧ ∀ c ∈ seg, c ≠ 47 := by
  have hs : segOk seg = true := h
  refine ⟨fun he => by rw [he] at hs; simp [segOk] at hs, fun c hc => ?_⟩
  unfold segOk at hs
  simp only [Bool.and_eq_true] at hs
  have hall := hs.2
  rw [List.all_eq_true] at hall
  have hcc := hall c hc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcc
  exact hcc.1

/-- **A normalised request URI is rooted and same-origin.** `$uri` always begins with exactly one
`/`: its first byte is `/` and its second byte, if any, is not `/`. So `//evil.com/x` normalises
to `/evil.com/x`, and `return 301 $uri` can never become a protocol-relative redirect to another
host. -/
theorem uri_rooted (np : NPath) (hs : ∀ s ∈ np.segs, Safe s) :
    np.uri.head? = some 47 ∧ np.uri.tail.head? ≠ some 47 := by
  cases hseg : np.segs with
  | nil => simp [NPath.uri, hseg]
  | cons seg rest =>
    have hsafe : Safe seg := hs seg (hseg ▸ List.mem_cons_self)
    obtain ⟨hne, hslash⟩ := safe_props seg hsafe
    cases hs2 : seg with
    | nil => exact absurd hs2 hne
    | cons c s' =>
      have hc : c ≠ 47 := hslash c (hs2 ▸ List.mem_cons_self)
      refine ⟨?_, ?_⟩
      · simp [NPath.uri, hseg, hs2, List.flatMap_cons]
      · simp only [NPath.uri, hseg, hs2, List.flatMap_cons, List.isEmpty_cons, Bool.not_false,
          Bool.and_true, List.cons_append, List.append_assoc, List.append_nil,
          List.tail_cons, List.head?_cons, ne_eq, Option.some.injEq]
        exact hc

/-- `isSuffixB s b` means `b` genuinely ends in `s`. -/
theorem isSuffixB_sound (s b : Bytes) (h : isSuffixB s b = true) : ∃ p, b = p ++ s := by
  unfold isSuffixB at h
  rw [List.isPrefixOf_iff_prefix] at h
  obtain ⟨t, ht⟩ := h
  refine ⟨t.reverse, ?_⟩
  have hh := congrArg List.reverse ht
  simp only [List.reverse_append, List.reverse_reverse] at hh
  exact hh.symm

end LeanNginx.Proofs
