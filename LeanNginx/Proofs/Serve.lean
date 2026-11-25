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
    (own : NPath → Bool) (o : Bytes → Option Kind) :
    ∀ items p, (tryFiles l eff v q own items).run o = .autoindex p → eff.autoindex = some true
  | [], p, h => by simp [tryFiles, Step.run] at h
  | [last], p, h => by
    simp only [tryFiles] at h
    split at h
    · simp [Step.run] at h
    · split at h <;> simp [Step.run] at h
  | item :: r :: rs, p, h => by
    have ih := tryFiles_autoindex l eff v q own o (r :: rs) p
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
          · split at h <;> simp [Step.run] at h
        · split at h
          · split at h
            · exact serveDir_autoindex eff _ _ _ o _ p h
            · simp [Step.run] at h
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
        · exact tryFiles_autoindex _ _ _ _ _ o _ p hr
        · exact serveStatic_autoindex _ _ _ _ o p hr

/-! ## Which file is served -/

theorem normalizeDecoded_file_uri (d : Bytes) (np : NPath) (h : normalizeDecoded d = some np)
    (hd : np.dir = false) : np.uri = joinSegs np.segs := by
  unfold normalizeDecoded at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨segs, _, rfl⟩ := h
    simp only [Bool.or_eq_false_iff] at hd
    have hne : segs.isEmpty = false := hd.2
    simp [NPath.uri, joinSegs, hne, hd.1]
  · cases h

theorem normalizePath_file_uri (raw : Bytes) (np : NPath) (h : normalizePath raw = some np)
    (hd : np.dir = false) : np.uri = joinSegs np.segs := by
  obtain ⟨d, _, hn⟩ := normalizePath_decoded raw np h
  exact normalizeDecoded_file_uri d np hn hd

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

theorem safe_plain (s : Bytes) (hok : Safe s) :
    s.isEmpty = false ∧ (s == b!".") = false ∧ (s == b!"..") = false := by
  simp only [Safe, segOk, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, _⟩ := hok
  exact ⟨h1, by simpa using h2, by simpa using h3⟩

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

/-! ## `$uri` read back as a path: the same segments, nothing decoded -/

theorem normSegs_empties : ∀ (k : Nat) (acc : List Bytes),
    normSegs (List.replicate k []) acc = some acc.reverse
  | 0, acc => by simp [normSegs]
  | k + 1, acc => by simp [List.replicate_succ, normSegs, normSegs_empties k acc]

/-- Safe segments followed by empty ones (trailing slashes) normalise to the safe segments. -/
theorem normSegs_safe_empties : ∀ (segs acc : List Bytes) (k : Nat), (∀ s ∈ segs, Safe s) →
    normSegs (segs ++ List.replicate k []) acc = some (acc.reverse ++ segs)
  | [], acc, k, _ => by simp [normSegs_empties]
  | s :: rest, acc, k, hs => by
    have hok : segOk s = true := hs s List.mem_cons_self
    have ih := normSegs_safe_empties rest (s :: acc) k
      (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    have h1 : s.isEmpty = false ∧ (s == b!".") = false ∧ (s == b!"..") = false := by
      simp only [segOk, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hok
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, _⟩ := hok
      exact ⟨h1, by simpa using h2, by simpa using h3⟩
    simp [normSegs, h1.1, h1.2.1, h1.2.2, hok, ih]

theorem joinSegs_empties (segs : List Bytes) (k : Nat) :
    joinSegs (segs ++ List.replicate k []) = joinSegs segs ++ List.replicate k 47 := by
  induction k with
  | zero => simp [joinSegs]
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc]
    simp only [joinSegs, List.flatMap_append] at ih ⊢
    rw [ih, List.replicate_succ']
    simp

theorem normalizeDecoded_of_segs (d : Bytes) (segs : List Bytes) (hd : d.head? = some 47)
    (hn : normSegs (splitOnByte 47 d) [] = some segs) :
    normalizeDecoded d = some ⟨segs, lastSegDir d || segs.isEmpty⟩ := by
  cases d with
  | nil => simp at hd
  | cons c d =>
    simp only [List.head?_cons, Option.some.injEq] at hd
    subst hd
    simp [normalizeDecoded, hn]

theorem split_join_empties (segs : List Bytes) (hs : ∀ s ∈ segs, Safe s) (k : Nat) :
    splitOnByte 47 (joinSegs (segs ++ List.replicate k [])) = [] :: (segs ++ List.replicate k []) := by
  have := splitOnByte_joinSegs (segs ++ List.replicate k []) [] (by simp) (by
    intro r hr
    cases List.mem_append.mp hr with
    | inl e => exact safe_no_slash r (hs r e)
    | inr e => rw [(List.mem_replicate.mp e).2]; simp)
  simpa using this

/-- `/seg₁/…/segₙ` (n ≥ 1) is read back as those segments, a file path. -/
theorem normalizeDecoded_join (segs : List Bytes) (hs : ∀ s ∈ segs, Safe s) (hne : segs ≠ []) :
    normalizeDecoded (joinSegs segs) = some ⟨segs, false⟩ := by
  have hsp := split_join_empties segs hs 0
  simp only [List.replicate_zero, List.append_nil] at hsp
  have hhead : (joinSegs segs).head? = some 47 := by
    cases segs with
    | nil => exact absurd rfl hne
    | cons a r => simp [joinSegs]
  have hn : normSegs (splitOnByte 47 (joinSegs segs)) [] = some segs := by
    rw [hsp]; simpa [normSegs] using normSegs_safe_id segs [] hs
  rw [normalizeDecoded_of_segs _ segs hhead hn]
  have hlast : lastSegDir (joinSegs segs) = false := by
    unfold lastSegDir
    rw [hsp]
    obtain ⟨x, hx⟩ : ∃ x, segs.getLast? = some x := by
      cases h : segs.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
      | some x => exact ⟨x, rfl⟩
    have hxs := safe_plain x (hs x (List.mem_of_getLast? hx))
    simp [List.getLast?_cons, hx, hxs.1, hxs.2.1, hxs.2.2]
  have hemp : segs.isEmpty = false := by cases segs <;> simp_all
  simp [hlast, hemp]

/-- `/seg₁/…/segₙ` followed by one or more `/` is read back as those segments, a directory. -/
theorem normalizeDecoded_join_slashes (segs : List Bytes) (hs : ∀ s ∈ segs, Safe s) (k : Nat) :
    normalizeDecoded (joinSegs segs ++ List.replicate (k + 1) 47) = some ⟨segs, true⟩ := by
  rw [← joinSegs_empties]
  have hsp := split_join_empties segs hs (k + 1)
  have hhead : (joinSegs (segs ++ List.replicate (k + 1) [])).head? = some 47 := by
    cases segs <;> simp [joinSegs, List.replicate_succ]
  have hn : normSegs (splitOnByte 47 (joinSegs (segs ++ List.replicate (k + 1) []))) [] =
      some segs := by
    rw [hsp]; simpa [normSegs] using normSegs_safe_empties segs [] (k + 1) hs
  rw [normalizeDecoded_of_segs _ segs hhead hn]
  have hlast : lastSegDir (joinSegs (segs ++ List.replicate (k + 1) [])) = true := by
    unfold lastSegDir
    rw [hsp, List.replicate_succ', ← List.append_assoc, ← List.cons_append, List.getLast?_concat]
    rfl
  simp [hlast]

theorem uri_of_dir (np : NPath) (hd : np.dir = true) : np.uri = joinSegs np.segs ++ [47] := by
  cases hs : np.segs <;> simp [NPath.uri, joinSegs, hd, hs]

theorem uri_of_file (np : NPath) (hd : np.dir = false) (hne : np.segs ≠ []) :
    np.uri = joinSegs np.segs := by
  cases hs : np.segs with
  | nil => exact absurd hs hne
  | cons a r => simp [NPath.uri, joinSegs, hd, hs]

/-- Normalising `$uri` gives back the path it was made from. -/
theorem normalizeDecoded_uri (np : NPath) (hs : ∀ s ∈ np.segs, Safe s)
    (hroot : np.segs = [] → np.dir = true) : normalizeDecoded np.uri = some np := by
  obtain ⟨segs, dir⟩ := np
  cases dir with
  | true => rw [uri_of_dir _ rfl]; exact normalizeDecoded_join_slashes segs hs 0
  | false =>
    have hne : segs ≠ [] := fun he => by simpa using hroot he
    rw [uri_of_file _ rfl hne]; exact normalizeDecoded_join segs hs hne

/-- `$uri/` is the same segments, as a directory. -/
theorem normalizeDecoded_uri_slash (np : NPath) (hs : ∀ s ∈ np.segs, Safe s) :
    normalizeDecoded (np.uri ++ [47]) = some ⟨np.segs, true⟩ := by
  obtain ⟨segs, dir⟩ := np
  cases dir with
  | true =>
    rw [uri_of_dir _ rfl, List.append_assoc]; exact normalizeDecoded_join_slashes segs hs 1
  | false =>
    cases segs with
    | nil => decide
    | cons a r =>
      rw [uri_of_file _ rfl (by simp)]; exact normalizeDecoded_join_slashes (a :: r) hs 0

theorem normalizeDecoded_root_dir (d : Bytes) (np : NPath) (h : normalizeDecoded d = some np) :
    np.segs = [] → np.dir = true := by
  unfold normalizeDecoded at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨segs, _, rfl⟩ := h
    intro he
    simp only at he
    simp [he]
  · cases h

/-! ## `try_files $uri $uri/ …` -/

theorem expand_uri (v : Vars) : expand v b!"$uri" = v.uri := by
  simp [expand, expandAux, takeVarName, isVarChar, isAlpha, isUpper, isLowerA, isDigit, Vars.lookup]

theorem expand_uri_slash (v : Vars) : expand v b!"$uri/" = v.uri ++ [47] := by
  simp [expand, expandAux, takeVarName, isVarChar, isAlpha, isUpper, isLowerA, isDigit, Vars.lookup]

theorem serveDir_ne_file (eff : Settings) (np : NPath) (base : Bytes) (segs : List Bytes)
    (o : Bytes → Option Kind) :
    ∀ idxs p size mtime, (serveDir eff np base segs idxs).run o ≠ .file p size mtime
  | [], p, size, mtime, h => by
    simp only [serveDir, Step.run] at h
    revert h
    generalize o (base ++ joinSegs segs) = r
    intro h
    rcases r with _ | ⟨_, _⟩ | _ <;> simp [Step.run] at h
    split at h <;> cases h
  | idx :: rest, p, size, mtime, h => by
    simp only [serveDir] at h
    split at h
    · simp only [Step.run] at h
      revert h
      generalize o (base ++ joinSegs (segs ++ [idx])) = r
      intro h
      rcases r with _ | ⟨_, _⟩ | _ <;> simp only [Step.run] at h
      all_goals first | exact serveDir_ne_file eff np base segs o rest p size mtime h | cases h
    · exact serveDir_ne_file eff np base segs o rest p size mtime h

theorem retAction_ne_file (v : Vars) (r : Nat × Option Bytes) (p : Bytes) (size : Nat)
    (mtime : Int) : (Step.done (retAction v r)).run o ≠ .file p size mtime := by
  unfold retAction
  split
  · simp [Step.run]
  · split <;> simp [Step.run]
  · simp [Step.run]

/-- `try_files` whose entries before the fallback are all `$uri` or `$uri/`, in a location with a
`root`: the only file it can serve is `root` followed by the request's own segments. -/
theorem tryFiles_uri_file (l : Location) (eff : Settings) (v : Vars) (q : Option Bytes)
    (own : NPath → Bool) (np : NPath) (hs : ∀ s ∈ np.segs, Safe s) (hroot : np.segs = [] → np.dir = true)
    (hv : v.uri = np.uri) (hal : l.alias = none) (o : Bytes → Option Kind) (last : Bytes) :
    ∀ (items : List Bytes), (∀ i ∈ items, i = b!"$uri" ∨ i = b!"$uri/") →
    ∀ p size mtime, (tryFiles l eff v q own (items ++ [last])).run o = .file p size mtime →
      np.dir = false ∧ p = dropTrailingSlash (eff.root.getD defaultRoot) ++ joinSegs np.segs := by
  intro items
  induction items with
  | nil =>
    intro _ p size mtime h
    simp only [List.nil_append, tryFiles] at h
    split at h
    · simp [Step.run] at h
    · split at h <;> simp [Step.run] at h
  | cons item rest ih =>
    intro hi p size mtime h
    have ih' := ih (fun i hm => hi i (List.mem_cons_of_mem _ hm)) p size mtime
    obtain ⟨r, rs, hrs⟩ : ∃ r rs, rest ++ [last] = r :: rs := by
      cases rest with
      | nil => exact ⟨last, [], rfl⟩
      | cons a t => exact ⟨a, t ++ [last], rfl⟩
    rw [hrs] at ih'
    rw [List.cons_append, hrs] at h
    simp only [tryFiles] at h
    rcases hi item List.mem_cons_self with rfl | rfl
    · simp only [expand_uri, hv, normalizeDecoded_uri np hs hroot, fsTarget, hal, Step.run] at h
      revert h
      generalize o _ = res
      intro h
      rcases res with _ | ⟨_, _⟩ | _ <;> simp only at h
      · exact ih' h
      · split at h
        · exact ih' h
        · rename_i hd
          split at h
          · simp only [Step.run, Action.file.injEq] at h
            exact ⟨by simpa using hd, h.1.symm⟩
          · simp [Step.run] at h
      · split at h
        · split at h
          · exact absurd h (serveDir_ne_file _ _ _ _ o _ p size mtime)
          · simp [Step.run] at h
        · exact ih' h
    · simp only [expand_uri_slash, hv, normalizeDecoded_uri_slash np hs, fsTarget, hal, Step.run] at h
      revert h
      generalize o _ = res
      intro h
      rcases res with _ | ⟨_, _⟩ | _ <;> simp only [↓reduceIte] at h
      · exact ih' h
      · exact ih' h
      · split at h
        · exact absurd h (serveDir_ne_file _ _ _ _ o _ p size mtime)
        · simp [Step.run] at h

/-! ## A served file belongs to the location that was selected -/

/-- `p` is the file the path `np` names in location `l`. -/
def FileOf (l : Location) (eff : Settings) (np : NPath) (p : Bytes) : Prop :=
  ∃ base segs, fsTarget l eff np = some (base, segs) ∧ p = base ++ joinSegs segs

/-- A file served by `try_files` is the file of an entry path that `own` accepts. -/
theorem tryFiles_file_owned (l : Location) (eff : Settings) (v : Vars) (q : Option Bytes)
    (own : NPath → Bool) (o : Bytes → Option Kind) :
    ∀ items p size mtime, (tryFiles l eff v q own items).run o = .file p size mtime →
      ∃ np', own np' = true ∧ FileOf l eff np' p
  | [], p, size, mtime, h => by simp [tryFiles, Step.run] at h
  | [last], p, size, mtime, h => by
    simp only [tryFiles] at h
    split at h
    · simp [Step.run] at h
    · split at h <;> simp [Step.run] at h
  | item :: r :: rs, p, size, mtime, h => by
    have ih := tryFiles_file_owned l eff v q own o (r :: rs) p size mtime
    simp only [tryFiles] at h
    split at h
    · exact ih h
    · rename_i np _
      split at h
      · exact ih h
      · rename_i base segs ht
        simp only [Step.run] at h
        revert h
        generalize o _ = res
        intro h
        rcases res with _ | ⟨_, _⟩ | _ <;> simp only at h
        · exact ih h
        · split at h
          · exact ih h
          · split at h
            · rename_i hown
              simp only [Step.run, Action.file.injEq] at h
              exact ⟨np, hown, base, segs, ht, h.1.symm⟩
            · simp [Step.run] at h
        · split at h
          · split at h
            · exact absurd h (serveDir_ne_file _ _ _ _ o _ p size mtime)
            · simp [Step.run] at h
          · exact ih h

/-- Without `try_files`, the file served is the request path's own. -/
theorem serveStatic_file_own (l : Location) (eff : Settings) (np : NPath) (q : Option Bytes)
    (o : Bytes → Option Kind) (p : Bytes) (size : Nat) (mtime : Int)
    (h : (serveStatic l eff np q).run o = .file p size mtime) : FileOf l eff np p := by
  unfold serveStatic at h
  split at h
  · simp [Step.run] at h
  · rename_i base segs ht
    split at h
    · exact absurd h (serveDir_ne_file _ _ _ _ o _ p size mtime)
    · simp only [Step.run] at h
      revert h
      generalize o _ = res
      intro h
      rcases res with _ | ⟨_, _⟩ | _ <;> simp [Step.run] at h
      exact ⟨base, segs, ht, h.1.symm⟩

/-- Whatever `route` serves is the file, in the selected location, of a path that selects that
same location. -/
theorem route_file_own (h : HttpConf) (sv : Server) (req : Request) (v : Vars) (np : NPath)
    (o : Bytes → Option Kind) (p : Bytes) (size : Nat) (mtime : Int)
    (hr : (route h sv req v np).run o = .file p size mtime) :
    let l := (selectLocation sv.locations np.uri).getD defaultLocation
    ∃ np', (selectLocation sv.locations np'.uri).getD defaultLocation = l ∧
      FileOf l (effective h sv l) np' p := by
  intro l
  unfold route at hr
  split at hr
  · exact absurd hr (retAction_ne_file _ _ _ _ _)
  · simp only at hr
    split at hr
    · exact absurd hr (retAction_ne_file _ _ _ _ _)
    · simp [Step.run] at hr
    · split at hr
      · simp [Step.run] at hr
      · split at hr
        · obtain ⟨np', hown, hf⟩ := tryFiles_file_owned _ _ _ _ _ o _ p size mtime hr
          exact ⟨np', by simpa using hown, hf⟩
        · exact ⟨np, rfl, serveStatic_file_own _ _ _ _ o p size mtime hr⟩

end Proofs
end LeanNginx
