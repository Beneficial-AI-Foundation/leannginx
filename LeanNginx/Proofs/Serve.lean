import LeanNginx.Proofs.Route
/-! Lemmas about serving files: which file is served, when a directory is listed, and that
answers about paths outside the served directory cannot change the result. -/

set_option linter.unusedSimpArgs false

namespace LeanNginx
namespace Proofs

/-! ## Non-interference -/

/-- A program confined to `P` gives the same action under two file systems that agree on `P`. -/
theorem run_congr (P : Bytes → Prop) (o₁ o₂ : Bytes → Option Kind)
    (hag : ∀ p, P p → o₁ p = o₂ p) : ∀ s : Step, s.Confined P → s.run o₁ = s.run o₂
  | .done _, _ => rfl
  | .stat p k, h => by
    simp only [Step.run]
    rw [hag p h.1]
    exact run_congr P o₁ o₂ hag (k (o₂ p)) (h.2 (o₂ p))

/-! ## Directory listings -/

theorem serveDir_autoindex (eff : Settings) (np : NPath) (base : Bytes) (segs : List Bytes)
    (o : Bytes → Option Kind) :
    ∀ idxs p, (serveDir eff np base segs idxs).run o = .autoindex p → eff.autoindex = some true
  | [], p, h => by
    simp only [serveDir, Step.run] at h
    revert h
    generalize o (base ++ joinSegs segs) = r
    intro h
    rcases r with _ | ⟨_, _⟩ | _ <;> simp [Step.run] at h
    rcases ha : eff.autoindex with _ | b
    · simp [ha] at h
    · cases b <;> simp_all
  | idx :: rest, p, h => by
    simp only [serveDir] at h
    split at h
    · simp only [Step.run] at h
      revert h
      generalize o (base ++ joinSegs (segs ++ [idx])) = r
      intro h
      rcases r with _ | ⟨_, _⟩ | _ <;> simp only [Step.run] at h
      all_goals first | exact serveDir_autoindex eff np base segs o rest p h | cases h
    · exact serveDir_autoindex eff np base segs o rest p h

theorem tryFiles_autoindex (l : Location) (eff : Settings) (v : Vars) (q : Option Bytes)
    (o : Bytes → Option Kind) :
    ∀ items p, (tryFiles l eff v q items).run o = .autoindex p → eff.autoindex = some true
  | [], p, h => by simp [tryFiles, Step.run] at h
  | [last], p, h => by
    simp only [tryFiles] at h
    split at h <;> simp [Step.run] at h
  | item :: r :: rs, p, h => by
    have ih := tryFiles_autoindex l eff v q o (r :: rs) p
    simp only [tryFiles] at h
    split at h
    · exact ih h
    · split at h
      · exact ih h
      · simp only [Step.run] at h
        revert h
        generalize o _ = res
        intro h
        rcases res with _ | ⟨_, _⟩ | _ <;> simp only at h
        · exact ih h
        · split at h
          · exact ih h
          · simp [Step.run] at h
        · split at h
          · exact serveDir_autoindex eff _ _ _ o _ p h
          · exact ih h

theorem serveStatic_autoindex (l : Location) (eff : Settings) (np : NPath) (q : Option Bytes)
    (o : Bytes → Option Kind) (p : Bytes)
    (h : (serveStatic l eff np q).run o = .autoindex p) : eff.autoindex = some true := by
  unfold serveStatic at h
  split at h
  · simp [Step.run] at h
  · split at h
    · exact serveDir_autoindex eff np _ _ o _ p h
    · simp only [Step.run] at h
      revert h
      generalize o _ = res
      intro h
      rcases res with _ | ⟨_, _⟩ | _ <;> simp [Step.run] at h

theorem retAction_ne_autoindex (v : Vars) (r : Nat × Option Bytes) (p : Bytes) :
    retAction v r ≠ .autoindex p := by
  unfold retAction
  split
  · simp
  · split <;> simp
  · simp

theorem route_autoindex' (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (np : NPath)
    (o : Bytes → Option Kind) (p : Bytes)
    (hr : (route h sv req v np).run o = .autoindex p) :
    let l := (selectLocation sv.locations np.uri).getD defaultLocation
    (effective h sv l).autoindex = some true := by
  intro l
  unfold route at hr
  split at hr
  · exact absurd hr (retAction_ne_autoindex _ _ _)
  · simp only at hr
    split at hr
    · exact absurd hr (retAction_ne_autoindex _ _ _)
    · simp [Step.run] at hr
    · split at hr
      · simp [Step.run] at hr
      · split at hr
        · exact tryFiles_autoindex _ _ _ _ o _ p hr
        · exact serveStatic_autoindex _ _ _ _ o p hr

/-! ## Which file is served -/

theorem normalizePath_file_uri (raw : Bytes) (np : NPath) (h : normalizePath raw = some np)
    (hd : np.dir = false) : np.uri = joinSegs np.segs := by
  unfold normalizePath at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨d, _, segs, _, rfl⟩ := h
    simp only [Bool.or_eq_false_iff] at hd
    have hne : segs.isEmpty = false := hd.2
    simp [NPath.uri, joinSegs, hne, hd.1]
  · cases h

/-- With no `return`, `proxy_pass` or `try_files` in play, a GET/HEAD for a file path stats
exactly one path and answers from it. -/
theorem route_static (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (np : NPath)
    (o : Bytes → Option Kind) (l : Location) (base : Bytes) (segs : List Bytes)
    (hl : (selectLocation sv.locations np.uri).getD defaultLocation = l)
    (hsv : sv.ret = none) (hret : l.ret = none) (hpx : l.proxy = none) (htf : l.tryFiles = none)
    (hm : req.method = b!"GET" ∨ req.method = b!"HEAD") (hd : np.dir = false)
    (ht : fsTarget l (effective h sv l) np = some (base, segs)) :
    (route h sv req v np).run o =
      match o (base ++ joinSegs segs) with
      | some (.file size mtime) => .file (base ++ joinSegs segs) size mtime
      | some .dir => .redirect 301 (withQuery (percentEncode (np.uri ++ [47])) req.query)
      | none => .error 404 := by
  have hm' : (req.method == b!"GET" || req.method == b!"HEAD") = true := by
    rcases hm with hm | hm <;> simp [hm]
  unfold route
  simp only [hsv, hl, hret, hpx, htf, hm', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold serveStatic
  simp only [ht, hd, Bool.false_eq_true, ↓reduceIte, Step.run]
  generalize o (base ++ joinSegs segs) = r
  rcases r with _ | ⟨_, _⟩ | _ <;> rfl

/-! ## `alias`: splitting `/seg₁/…/segₙ` back into segments -/

theorem splitOnByte_joinSegs : ∀ (rest : List Bytes) (s : Bytes),
    (∀ c ∈ s, c ≠ 47) → (∀ r ∈ rest, ∀ c ∈ r, c ≠ 47) →
    splitOnByte 47 (s ++ joinSegs rest) = s :: rest
  | rest, [], _, hr => by
    cases rest with
    | nil => simp [joinSegs, splitOnByte]
    | cons r rs =>
      have := splitOnByte_joinSegs rs r (hr r List.mem_cons_self)
        (fun x hx => hr x (List.mem_cons_of_mem _ hx))
      simp only [joinSegs, List.flatMap_cons, List.nil_append, List.cons_append] at this ⊢
      simp [splitOnByte, this]
  | rest, c :: s, hs, hr => by
    have ih := splitOnByte_joinSegs rest s (fun x hx => hs x (List.mem_cons_of_mem _ hx)) hr
    have hc : (c == 47) = false := by simpa using hs c List.mem_cons_self
    simp [splitOnByte, hc, ih]

theorem normSegs_safe_id : ∀ (segs acc : List Bytes), (∀ s ∈ segs, Safe s) →
    normSegs segs acc = some (acc.reverse ++ segs)
  | [], acc, _ => by simp [normSegs]
  | s :: rest, acc, hs => by
    have hok : segOk s = true := hs s List.mem_cons_self
    have ih := normSegs_safe_id rest (s :: acc) (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    have h1 : s.isEmpty = false ∧ (s == b!".") = false ∧ (s == b!"..") = false := by
      simp only [segOk, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hok
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, _⟩ := hok
      exact ⟨h1, by simpa using h2, by simpa using h3⟩
    simp [normSegs, h1.1, h1.2.1, h1.2.2, hok, ih]

theorem safe_no_slash (s : Bytes) (h : Safe s) : ∀ c ∈ s, c ≠ 47 := by
  intro c hc
  simp only [Safe, segOk, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 c hc
  simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

/-- The remainder after an alias location's prefix maps back to the request's segments. -/
theorem alias_segs (p rest : List Bytes) (luri : Bytes) (hall : ∀ s ∈ p ++ rest, Safe s)
    (hl : luri = joinSegs p ∨ luri = joinSegs p ++ [47]) (hne : rest ≠ []) :
    normSegs (splitOnByte 47 ((joinSegs (p ++ rest)).drop luri.length)) [] = some rest := by
  have hr : ∀ s ∈ rest, Safe s := fun s hs => hall s (List.mem_append_right _ hs)
  have hns : ∀ r ∈ rest, ∀ c ∈ r, c ≠ 47 := fun r hr' => safe_no_slash r (hr r hr')
  have hj : joinSegs (p ++ rest) = joinSegs p ++ joinSegs rest := by simp [joinSegs]
  rcases hl with rfl | rfl
  · rw [hj, List.drop_left]
    have := splitOnByte_joinSegs rest [] (by simp) hns
    simp only [List.nil_append] at this
    rw [this]
    simp [normSegs, normSegs_safe_id rest [] hr]
  · obtain ⟨r, rs, rfl⟩ : ∃ r rs, rest = r :: rs := by
      cases rest with | nil => exact absurd rfl hne | cons r rs => exact ⟨r, rs, rfl⟩
    have e : joinSegs (p ++ r :: rs) = (joinSegs p ++ [47]) ++ (r ++ joinSegs rs) := by
      simp [joinSegs]
    rw [e, List.drop_left]
    rw [splitOnByte_joinSegs rs r (hns r List.mem_cons_self)
      (fun x hx => hns x (List.mem_cons_of_mem _ hx))]
    exact normSegs_safe_id (r :: rs) [] hr

end Proofs
end LeanNginx
