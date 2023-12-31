
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros p np,
  apply np,
  exact p,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro nnp,
  by_cases p : P, -- ⛤ LEM
    exact p,

    exfalso,
    apply nnp,
    exact p,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
    apply doubleneg_elim P,

    apply doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pq,
  cases pq with p q,
    right,
    exact p,

    left,
    exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pq,
  cases pq with p q,
  split,
    exact q,

    exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros npq p,
  cases npq with np q,
    exfalso,
    apply np p,

    exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros pq np,
  cases pq with p q,
    contradiction,

    exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros pq nq p,
  have q : Q := pq(p),
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros nqnp p,
  by_contradiction nq, -- ⛤ RAA
  have np : ¬P := nqnp(nq),
  apply np p,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
    apply impl_as_contrapositive P Q,

    apply impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro n_pnp,
  apply n_pnp,
  right,
  intro p,
  apply n_pnp,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros pqp np,
  apply np,
  apply pqp,
  intro p,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros pq npnq,
  cases npnq with np nq,
  cases pq with p q,
    contradiction,

    contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros pq npnq,
  cases pq with p q,
  cases npnq,
    contradiction,

    contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npq,
  split,
    intro p,
    apply npq,
    left,
    exact p,

    intro q,
    apply npq,
    right,
    exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros npnq pq,
  cases npnq with np nq,
  cases pq with p q,
    contradiction,

    contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro n_pq,
  by_cases h : Q, -- ⛤ LEM
    right,
    intro p,
    apply n_pq,
    split,
      exact p,

      exact h,
    
    left,
    exact h,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros nqnp pq,
  cases pq with p q,
  cases nqnp with nq np,
    contradiction,

    contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
    apply demorgan_conj P Q,

    apply demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
    apply demorgan_disj P Q,

    apply demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro pqr,
  cases pqr with p qr,
  cases qr with q r,
    left,
    split,
      exact p,

      exact q,

    right,
    split,
      exact p,

      exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pqpr,
  cases pqpr with pq pr,
    split,
      exact pq.1,

      left,
      exact pq.2,

    split,
      exact pr.1,

      right,
      exact pr.2,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro pqr,
  split,
    cases pqr with p qr,
      left,
      exact p,

      right,
      exact qr.1,

    cases pqr with p qr,
      left,
      exact p,

      right,
      exact qr.2,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pqpr,
  cases pqpr with pq pr,
  cases pq with p q,
    left,
    exact p,

    cases pr with p r,
      left,
      exact p,

      right,
      split,
        exact q,

        exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros pqr p q,
  apply pqr,
  split,
    exact p,

    exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros pqr pq,
  cases pq with p q,
  apply pqr,
  exact p,
  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  exact pq.1,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  exact pq.2,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
    intro pp,
    exact pp.1,

    intro p,
    split,
      exact p,

      exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
    intro pp,
    cases pp with p p,
      exact p,

      exact p,

    intro p,
    left,
    exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros hi u pu,
  apply hi,
  existsi u,
  exact pu,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros h1 h2,
  cases h2 with x px,
  apply h1 x px,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  by_contradiction h1, -- ⛤ RAA
  apply h,
  intro x,
  by_contradiction px, -- ⛤ RAA
  apply h1,
  existsi x,
  exact px,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros h h1,
  cases h with x npx,
  have px : P x := h1(x),
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
    apply demorgan_forall U P,

    apply demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
    apply demorgan_exists U P,

    apply demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros h h1,
  cases h with x px,
  apply h1 x,
  exact px,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros h h1,
  cases h1 with x npx,
  have px : P x := h(x),
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros h x,
  by_contradiction npx, -- ⛤ RAA
  apply h,
  existsi x,
  exact npx,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h,
  by_contradiction h1, -- ⛤ RAA
  apply h,
  intros x px,
  apply h1,
  existsi x,
  exact px,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
    apply forall_as_neg_exists U P,

    apply forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
    apply exists_as_neg_forall U P,

    apply exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with x px_qx,
  cases px_qx with px qx,
  split,
    existsi x,
    exact px,

    existsi x,
    exact qx,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with x px_qx,
  cases px_qx with px qx,
    left,
    existsi x,
    exact px,

    right,
    existsi x,
    exact qx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with epx eqx,
    cases epx with x px,
    existsi x,
    left,
    exact px,

    cases eqx with x qx,
    existsi x,
    right,
    exact qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
    intro x,
    have px_qx : (P x ∧ Q x) := h(x),
    exact px_qx.1,

    intro x,
    have px_qx : (P x ∧ Q x) := h(x),
    exact px_qx.2,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intros h x,
  cases h with h1 h2,
  split,
    apply h1 x,

    apply h2 x,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros h x,
  cases h with h1 h2,
    left,
    apply h1 x,

    right,
    apply h2 x,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
