import LeanNginx.Proofs.Basic
/-! Lemmas about request routing: location selection and file-system confinement. -/

set_option linter.unusedSimpArgs false

namespace LeanNginx

/-- Every path a stat program asks about, serves, or lists satisfies `P`, whatever the
answers to its `stat` questions are. -/
def Step.Confined (P : Bytes → Prop) : Step → Prop
  | .done (.file p _ _) => P p
  | .done (.autoindex p) => P p
  | .done _ => True
  | .stat p k => P p ∧ ∀ r, (k r).Confined P

/-- `p` is `base/seg₁/…/segₙ` with every segment safe. -/
def Under (base p : Bytes) : Prop := ∃ segs, (∀ s ∈ segs, Safe s) ∧ p = base ++ joinSegs segs

/-- The directory a location serves from: its `alias`, else the effective `root`. -/
def baseOf (l : Location) (eff : Settings) : Bytes :=
  dropTrailingSlash (match l.alias with | some a => a | none => eff.root.getD defaultRoot)

/-- What a finished action touches on disk. -/
def Action.Touches (P : Bytes → Prop) : Action → Prop
  | .file p _ _ => P p
  | .autoindex p => P p
  | _ => True

/-- An internal redirect goes to a path made of safe segments (any other action: nothing to say). -/
def Action.RedirectSafe : Action → Prop
  | .internal np _ => ∀ s ∈ np.segs, Safe s
  | _ => True

/-- Whatever the answers to its `stat` questions are, a stat program that ends in an internal
redirect redirects to a path made of safe segments. -/
def Step.RedirectsSafe : Step → Prop
  | .done a => a.RedirectSafe
  | .stat _ k => ∀ r, (k r).RedirectsSafe

namespace Proofs

theorem confined_run (P : Bytes → Prop) (o : Bytes → Option Kind) :
    ∀ s : Step, s.Confined P → (s.run o).Touches P
  | .done a, h => by cases a <;> simp_all [Step.run, Step.Confined, Action.Touches]
  | .stat p k, h => by
    simp only [Step.run]
    exact confined_run P o (k (o p)) (h.2 (o p))

theorem serveDir_confined (eff : Settings) (np : NPath) (base : Bytes) (segs : List Bytes)
    (hs : ∀ s ∈ segs, Safe s) :
    ∀ idxs, (serveDir eff np base segs idxs).Confined (Under base)
  | [] => by
    simp only [serveDir, Step.Confined]
    refine ⟨⟨segs, hs, rfl⟩, ?_⟩
    intro r
    split
    · split <;> simp [Step.Confined] ; exact ⟨segs, hs, rfl⟩
    · simp [Step.Confined]
  | idx :: rest => by
    simp only [serveDir]
    split
    · rename_i hok
      simp only [Step.Confined]
      refine ⟨⟨segs ++ [idx], ?_, rfl⟩, ?_⟩
      · intro s hm
        cases List.mem_append.mp hm with
        | inl e => exact hs s e
        | inr e => simp at e; subst e; exact hok
      · intro r
        split
        · simp [Step.Confined]
        · exact serveDir_confined eff np base segs hs rest
    · exact serveDir_confined eff np base segs hs rest

theorem fsTarget_ok (l : Location) (eff : Settings) (np : NPath) (base : Bytes)
    (segs : List Bytes) (hnp : ∀ s ∈ np.segs, Safe s)
    (h : fsTarget l eff np = some (base, segs)) :
    base = baseOf l eff ∧ ∀ s ∈ segs, Safe s := by
  unfold fsTarget at h
  split at h
  · rename_i a ha
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨segs', hn, rfl, rfl⟩ := h
    exact ⟨by simp [baseOf, ha], Proofs.normSegs_safe _ [] _ (by simp) hn⟩
  · rename_i ha
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [baseOf, ha], hnp⟩

theorem serveStatic_confined (l : Location) (eff : Settings) (np : NPath) (q : Option Bytes)
    (hnp : ∀ s ∈ np.segs, Safe s) :
    (serveStatic l eff np q).Confined (Under (baseOf l eff)) := by
  unfold serveStatic
  split
  · simp [Step.Confined]
  · rename_i base segs ht
    obtain ⟨rfl, hs⟩ := fsTarget_ok l eff np _ _ hnp ht
    split
    · exact serveDir_confined eff np _ segs hs _
    · simp only [Step.Confined]
      refine ⟨⟨segs, hs, rfl⟩, ?_⟩
      intro r
      split <;> simp [Step.Confined]
      exact ⟨segs, hs, rfl⟩

theorem tryFiles_confined (l : Location) (eff : Settings) (v : Vars) (q : Option Bytes)
    (own : NPath → Bool) :
    ∀ items, (tryFiles l eff v q own items).Confined (Under (baseOf l eff))
  | [] => by simp [tryFiles, Step.Confined]
  | [last] => by
    simp only [tryFiles]
    split
    · simp [Step.Confined]
    · split <;> simp [Step.Confined]
  | item :: r :: rs => by
    have ih := tryFiles_confined l eff v q own (r :: rs)
    simp only [tryFiles]
    split
    · exact ih
    · rename_i np hnorm
      split
      · exact ih
      · rename_i base segs ht
        obtain ⟨rfl, hs⟩ := fsTarget_ok l eff np _ _ (normalizeDecoded_safe _ _ hnorm) ht
        simp only [Step.Confined]
        refine ⟨⟨segs, hs, rfl⟩, ?_⟩
        intro res
        split
        · split
          · exact ih
          · split
            · simp [Step.Confined]; exact ⟨segs, hs, rfl⟩
            · simp [Step.Confined]
        · split
          · split
            · exact serveDir_confined eff np _ segs hs _
            · simp [Step.Confined]
          · exact ih
        · exact ih

theorem retAction_confined (P : Bytes → Prop) (v : Vars) (r : Nat × Option Bytes) :
    (Step.done (retAction v r)).Confined P := by
  unfold retAction
  split
  · simp [Step.Confined]
  · split <;> simp [Step.Confined]
  · simp [Step.Confined]

theorem route_confined' (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (np : NPath)
    (hnp : ∀ s ∈ np.segs, Safe s) :
    let l := (selectLocation sv.locations np.uri).getD defaultLocation
    (route h sv req v np).Confined (Under (baseOf l (effective h sv l))) := by
  intro l
  unfold route
  split
  · exact retAction_confined _ _ _
  · simp only
    split
    · exact retAction_confined _ _ _
    · simp [Step.Confined]
    · split
      · simp [Step.Confined]
      · split
        · exact tryFiles_confined _ _ _ _ _ _
        · exact serveStatic_confined _ _ _ _ hnp

/-! ## Internal redirects -/

theorem internalTarget_safe (u : Bytes) (np : NPath) (q : Option Bytes)
    (h : internalTarget u = some (np, q)) : ∀ s ∈ np.segs, Safe s := by
  unfold internalTarget at h
  split at h
  rename_i p q' _
  cases hn : normalizeDecoded p with
  | none => simp [hn] at h
  | some np' =>
    simp only [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1 ▸ normalizeDecoded_safe p np' hn

theorem redirectsSafe_run (o : Bytes → Option Kind) :
    ∀ s : Step, s.RedirectsSafe → (s.run o).RedirectSafe
  | .done a, h => by cases a <;> simp_all [Step.run, Step.RedirectsSafe, Action.RedirectSafe]
  | .stat p k, h => by
    simp only [Step.run]
    exact redirectsSafe_run o (k (o p)) (h (o p))

theorem serveDir_redirects (eff : Settings) (np : NPath) (base : Bytes) (segs : List Bytes)
    (hnp : ∀ s ∈ np.segs, Safe s) :
    ∀ idxs, (serveDir eff np base segs idxs).RedirectsSafe
  | [] => by
    simp only [serveDir, Step.RedirectsSafe]
    intro r
    split
    · split <;> simp [Step.RedirectsSafe, Action.RedirectSafe]
    · simp [Step.RedirectsSafe, Action.RedirectSafe]
  | idx :: rest => by
    simp only [serveDir]
    split
    · rename_i hok
      simp only [Step.RedirectsSafe]
      intro r
      split
      · simp only [Step.RedirectsSafe, Action.RedirectSafe]
        intro s hm
        cases List.mem_append.mp hm with
        | inl e => exact hnp s e
        | inr e => simp at e; subst e; exact hok
      · exact serveDir_redirects eff np base segs hnp rest
    · exact serveDir_redirects eff np base segs hnp rest

theorem serveStatic_redirects (l : Location) (eff : Settings) (np : NPath) (q : Option Bytes)
    (hnp : ∀ s ∈ np.segs, Safe s) : (serveStatic l eff np q).RedirectsSafe := by
  unfold serveStatic
  split
  · simp [Step.RedirectsSafe, Action.RedirectSafe]
  · split
    · exact serveDir_redirects eff np _ _ hnp _
    · simp only [Step.RedirectsSafe]
      intro r
      split <;> simp [Step.RedirectsSafe, Action.RedirectSafe]

theorem tryFiles_redirects (l : Location) (eff : Settings) (v : Vars) (q : Option Bytes)
    (own : NPath → Bool) :
    ∀ items, (tryFiles l eff v q own items).RedirectsSafe
  | [] => by simp [tryFiles, Step.RedirectsSafe, Action.RedirectSafe]
  | [last] => by
    simp only [tryFiles]
    split
    · simp [Step.RedirectsSafe, Action.RedirectSafe]
    · split
      · rename_i np q' ht
        simpa [Step.RedirectsSafe, Action.RedirectSafe] using internalTarget_safe _ np q' ht
      · simp [Step.RedirectsSafe, Action.RedirectSafe]
  | item :: r :: rs => by
    have ih := tryFiles_redirects l eff v q own (r :: rs)
    simp only [tryFiles]
    split
    · exact ih
    · rename_i np hnorm
      split
      · exact ih
      · simp only [Step.RedirectsSafe]
        intro res
        split
        · split
          · exact ih
          · split
            · simp [Step.RedirectsSafe, Action.RedirectSafe]
            · simpa [Step.RedirectsSafe, Action.RedirectSafe] using normalizeDecoded_safe _ _ hnorm
        · split
          · split
            · exact serveDir_redirects eff np _ _ (normalizeDecoded_safe _ _ hnorm) _
            · simpa [Step.RedirectsSafe, Action.RedirectSafe] using normalizeDecoded_safe _ _ hnorm
          · exact ih
        · exact ih

theorem retAction_redirects (v : Vars) (r : Nat × Option Bytes) :
    (Step.done (retAction v r)).RedirectsSafe := by
  unfold retAction
  split
  · simp [Step.RedirectsSafe, Action.RedirectSafe]
  · split <;> simp [Step.RedirectsSafe, Action.RedirectSafe]
  · simp [Step.RedirectsSafe, Action.RedirectSafe]

theorem route_redirects' (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (np : NPath)
    (hnp : ∀ s ∈ np.segs, Safe s) : (route h sv req v np).RedirectsSafe := by
  unfold route
  split
  · exact retAction_redirects _ _
  · simp only
    split
    · exact retAction_redirects _ _
    · simp [Step.RedirectsSafe, Action.RedirectSafe]
    · split
      · simp [Step.RedirectsSafe, Action.RedirectSafe]
      · split
        · exact tryFiles_redirects _ _ _ _ _ _
        · exact serveStatic_redirects _ _ _ _ hnp

/-! ## Location selection -/

theorem longest_mem : ∀ (ls : List Location) (best : Option Location) (l : Location),
    longest ls best = some l → l ∈ ls ∨ best = some l
  | [], best, l, h => by simp [longest] at h; exact Or.inr h
  | x :: xs, best, l, h => by
    simp only [longest] at h
    rcases longest_mem xs _ l h with hm | hb
    · exact Or.inl (List.mem_cons_of_mem _ hm)
    · rcases best with _ | b
      · simp at hb; subst hb; exact Or.inl List.mem_cons_self
      · by_cases hlt : b.uri.length < x.uri.length
        · simp [hlt] at hb; subst hb; exact Or.inl List.mem_cons_self
        · simp [hlt] at hb; exact Or.inr (by rw [hb])

theorem longest_max : ∀ (ls : List Location) (best : Option Location) (l : Location),
    longest ls best = some l →
    (∀ x ∈ ls, x.uri.length ≤ l.uri.length) ∧ (∀ b, best = some b → b.uri.length ≤ l.uri.length)
  | [], best, l, h => by
    simp [longest] at h; subst h; simp
  | x :: xs, best, l, h => by
    simp only [longest] at h
    have ih := longest_max xs _ l h
    rcases best with _ | b
    · simp only at ih
      refine ⟨?_, by simp⟩
      intro y hy
      cases List.mem_cons.mp hy with
      | inl e => subst e; exact ih.2 _ rfl
      | inr e => exact ih.1 y e
    · by_cases hlt : b.uri.length < x.uri.length
      · simp only [hlt, ↓reduceIte] at ih
        have hx := ih.2 x rfl
        refine ⟨?_, ?_⟩
        · intro y hy
          cases List.mem_cons.mp hy with
          | inl e => subst e; exact hx
          | inr e => exact ih.1 y e
        · intro b' hb; cases hb; omega
      · simp only [hlt, ↓reduceIte] at ih
        have hb := ih.2 b rfl
        refine ⟨?_, ?_⟩
        · intro y hy
          cases List.mem_cons.mp hy with
          | inl e => subst e; omega
          | inr e => exact ih.1 y e
        · intro b' hb'; cases hb'; exact hb

end Proofs
end LeanNginx
