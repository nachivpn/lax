{-# OPTIONS --safe --without-K #-}

import Type
module SMLC.Term.Properties (𝕤 : Type.Ty) where

open import SMLC.Term.Base 𝕤

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)

wkTm-pres-⊆-refl : (t : Tm Γ a) → wkTm ⊆-refl t ≡ t
wkTm-pres-⊆-refl (var   v)   = cong  var (wkVar-pres-⊆-refl v)
wkTm-pres-⊆-refl (lam   t)   = cong  lam (wkTm-pres-⊆-refl  t)
wkTm-pres-⊆-refl (app   t u) = cong₂ app (wkTm-pres-⊆-refl  t) (wkTm-pres-⊆-refl u)
wkTm-pres-⊆-refl (return t)  = cong return (wkTm-pres-⊆-refl t)
wkTm-pres-⊆-refl (letin t u) = cong₂ letin (wkTm-pres-⊆-refl t) (wkTm-pres-⊆-refl u)
wkTm-pres-⊆-refl (get t)     = cong get (wkTm-pres-⊆-refl t)
wkTm-pres-⊆-refl (put t u)   = cong₂ put (wkTm-pres-⊆-refl t) (wkTm-pres-⊆-refl u)

wkTm-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (t : Tm Γ a)
  → wkTm (w ∙ w') t ≡ wkTm w' (wkTm w t)
wkTm-pres-⊆-trans w w' (var   v)   = cong  var (wkVar-pres-⊆-trans w w' v)
wkTm-pres-⊆-trans w w' (lam   t)   = cong  lam (wkTm-pres-⊆-trans (keep w) (keep  w') t)
wkTm-pres-⊆-trans w w' (app   t u) = cong₂ app (wkTm-pres-⊆-trans w w' t) (wkTm-pres-⊆-trans w w' u)
wkTm-pres-⊆-trans w w' (return t)  = cong return (wkTm-pres-⊆-trans w w' t) 
wkTm-pres-⊆-trans w w' (letin t u) = cong₂ letin (wkTm-pres-⊆-trans w w' t) (wkTm-pres-⊆-trans (keep w) (keep w') u)
wkTm-pres-⊆-trans w w' (get t)     = cong get (wkTm-pres-⊆-trans (keep w) (keep  w') t)
wkTm-pres-⊆-trans w w' (put t u)   = cong₂ put (wkTm-pres-⊆-trans w w' t) (wkTm-pres-⊆-trans w w' u)

wkSub-pres-⊆-refl : (s : Sub Γ Δ) → wkSub ⊆-refl s ≡ s
wkSub-pres-⊆-refl []       = refl
wkSub-pres-⊆-refl (s `, t) = cong₂ _`,_ (wkSub-pres-⊆-refl s) (wkTm-pres-⊆-refl t)

wkSub-unit-left = wkSub-pres-⊆-refl

wkSub-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (s : Sub Γ ΓR)
  → wkSub (w ∙ w') s ≡ wkSub w' (wkSub w s)
wkSub-pres-⊆-trans w w' []         = refl
wkSub-pres-⊆-trans w w' (s `, t)   = cong₂ _`,_ (wkSub-pres-⊆-trans w w' s) (wkTm-pres-⊆-trans w w' t)

private
  wkSubFreshLemma : {s : Sub Δ Γ} {w : Δ ⊆ Δ'}
    → wkSub freshWk[ Δ' , a ] (wkSub w s) ≡ wkSub (keep w) (drops s)
  wkSubFreshLemma {s = s} {w} = trans
    (trans
      (sym (wkSub-pres-⊆-trans _ _ _))
      (cong₂ wkSub (cong drop (trans (⊆-trans-unit-right _) (sym (⊆-trans-unit-left _)))) refl))
    (wkSub-pres-⊆-trans _ _ _)

substTm-nat : (t : Tm Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substTm (wkSub w s) t ≡ wkTm w (substTm s t)
substTm-nat (var x)           s          w
  = substVar-nat x s w
substTm-nat (lam {Γ} {a} t)   s          w
  = cong lam
      (trans
        (cong (λ s → substTm (s `, var zero) t) wkSubFreshLemma)
        (substTm-nat t (keeps s) (keep w)))
substTm-nat (app t u)         s          w
  = cong₂ app (substTm-nat t s w) (substTm-nat u s w)
substTm-nat (return t)        s          w
  = cong return (substTm-nat t s w) 
substTm-nat (letin t u)       s          w
  = cong₂ letin (substTm-nat t s w)
      (trans
        (cong (λ s → substTm (s `, var zero) u) wkSubFreshLemma)
        (substTm-nat u (keeps s) (keep w)))
substTm-nat (get t)           s          w
  = cong get ((trans
        (cong (λ s → substTm (s `, var zero) t) wkSubFreshLemma)
        (substTm-nat t (keeps s) (keep w))))
substTm-nat (put t u)         s          w
  = cong₂ put (substTm-nat t s w) (substTm-nat u s w)

assoc-substTm-wkTm : (t : Tm Γ a) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
    → substTm (trimSub w s) t ≡ substTm s (wkTm w t)
assoc-substTm-wkTm (var x)           s          w
  = assoc-substVar-wkVar x s w
assoc-substTm-wkTm (lam t)           s          w
  = cong lam (trans
    (cong (λ p → substTm (p `, var zero) t) (trimSub-nat s w freshWk))
    (assoc-substTm-wkTm t (keeps s) (keep w)))
assoc-substTm-wkTm (app t u)         s          w
  = cong₂ app (assoc-substTm-wkTm t s w) (assoc-substTm-wkTm u s w)
assoc-substTm-wkTm (return t)        s          w
  = cong return (assoc-substTm-wkTm t s w) 
assoc-substTm-wkTm (letin t u)       s          w
  = cong₂ letin
      (assoc-substTm-wkTm t s w)
      (trans
        (cong (λ p → substTm (p `, var zero) u) (trimSub-nat s w freshWk))
        (assoc-substTm-wkTm u (keeps s) (keep w)))
assoc-substTm-wkTm (get t)   s w
  = cong get ((trans
    (cong (λ p → substTm (p `, var zero) t) (trimSub-nat s w freshWk))
    (assoc-substTm-wkTm t (keeps s) (keep w))))
assoc-substTm-wkTm (put t u) s w
  = cong₂ put (assoc-substTm-wkTm t s w) (assoc-substTm-wkTm u s w)

assoc-substTm-trimSub = assoc-substTm-wkTm

private
  -- just a helper to reduce redundancy, nothing too interesting
  auxLemma : (w : Γ ⊆ Δ) → wkSub (drop[ a ] (w ∙ ⊆-refl)) ids ≡ drops (embWk w)

wkSub-unit-right : (w : Γ ⊆ Δ) → wkSub w ids ≡ embWk w
auxLemma w = (trans
    (wkSub-pres-⊆-trans w freshWk ids)
    (cong (wkSub freshWk) (wkSub-unit-right w)))

wkSub-unit-right base      = refl
wkSub-unit-right (drop w)  = trans
  (cong (λ w' → wkSub (drop w') ids) (sym (⊆-trans-unit-right w)))
  (auxLemma w)
wkSub-unit-right (keep w)  = cong (_`, var zero) (trans
  (sym (wkSub-pres-⊆-trans freshWk (keep w) ids))
  (trans
    (cong₂ wkSub (cong drop (trans (⊆-trans-unit-left _) (sym (⊆-trans-unit-right _)))) refl)
    (auxLemma w)))

substVar-pres-ids : (x : Var Γ a) → substVar ids x ≡ var x
substVar-pres-ids zero     = refl
substVar-pres-ids (succ x) = trans (substVar-nat x ids freshWk) (trans
  (cong (wkTm freshWk) (substVar-pres-ids x))
  (cong var (wkIncr x)))

substTm-pres-ids : (t : Tm Γ a) → substTm ids t ≡ t
substTm-pres-ids (var x)     = substVar-pres-ids x
substTm-pres-ids (lam t)     = cong lam (substTm-pres-ids t)
substTm-pres-ids (app t u)   = cong₂ app (substTm-pres-ids t) (substTm-pres-ids u)
substTm-pres-ids (return t)  = cong return (substTm-pres-ids t) 
substTm-pres-ids (letin t u) = cong₂ letin (substTm-pres-ids t) (substTm-pres-ids u)
substTm-pres-ids (get t)     = cong get (substTm-pres-ids t)
substTm-pres-ids (put t u)   = cong₂ put (substTm-pres-ids t) (substTm-pres-ids u)

-- TBD: rename
assoc-∙s-wkSub  : {Δ'' : Ctx} (s : Sub Δ Γ) (s' : Sub Δ' Δ) (w : Δ' ⊆ Δ'')
         → wkSub w (s ∙s s') ≡ s ∙s (wkSub w s')
assoc-∙s-wkSub []           s'             w
  = refl
assoc-∙s-wkSub (s `, x)     s'             w
  = cong₂ _`,_  (assoc-∙s-wkSub s s' w) (sym (substTm-nat x s' w))

-- TBD: rename
assoc-wkSub-∙s  : {Δ₁ : Ctx} (s : Sub Δ Γ) (s' : Sub Δ₁ Δ') (w : Δ ⊆ Δ')
         → s ∙s (trimSub w s') ≡ (wkSub w s) ∙s s'
assoc-wkSub-∙s []               s'          w
  = refl
assoc-wkSub-∙s (s `, x)         s'          w
  = cong₂ _`,_ (assoc-wkSub-∙s s s' w) (assoc-substTm-wkTm x s' w)
  
substVarPres∙s : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (x : Var Γ a)
  → substVar (s ∙s s') x ≡ substTm s' (substVar s x)
substVarPres∙s (s `, x) s' zero      = refl
substVarPres∙s (s `, x) s' (succ x₁) = substVarPres∙s s s' x₁

private
  dropKeepLemma : (s' : Sub Δ' Δ) (s : Sub Γ Δ')
           →  drops (s' ∙s s) ≡ drops {a = a} s' ∙s keeps s
  dropKeepLemma s' s = trans (assoc-∙s-wkSub s' s freshWk)
    (trans
      ((cong (s' ∙s_) (sym (trimSub-unit-left (drops s)))))
      (assoc-wkSub-∙s s' (keeps s) freshWk))
      
substTm-pres-∙s : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (t : Tm Γ a)
  → substTm (s ∙s s') t ≡ substTm s' (substTm s t)
substTm-pres-∙s s s'             (var x)
  = substVarPres∙s s s' x
substTm-pres-∙s s s'             (lam t)
  = cong lam
    (trans (cong ((λ s → substTm (s `, var zero) t)) ((dropKeepLemma s s')))
    (substTm-pres-∙s _ _ t))
substTm-pres-∙s s s'             (app t u)
  = cong₂ app (substTm-pres-∙s s s' t) (substTm-pres-∙s s s' u)
substTm-pres-∙s s s'             (return t)
  = cong return (substTm-pres-∙s s s' t) 
substTm-pres-∙s s s'             (letin t u)
  = cong₂ letin
      (substTm-pres-∙s s s' t)
      (trans
        (cong ((λ s → substTm (s `, var zero) u)) ((dropKeepLemma s s')))
        (substTm-pres-∙s _ _ u))
substTm-pres-∙s s s' (get t)
  = cong get ((trans (cong ((λ s → substTm (s `, var zero) t)) ((dropKeepLemma s s')))
    (substTm-pres-∙s _ _ t)))
substTm-pres-∙s s s' (put t u)
  = cong₂ put (substTm-pres-∙s s s' t) (substTm-pres-∙s s s' u)

∙s-unit-right : (s : Sub Γ Γ') → s ∙s ids ≡ s
∙s-unit-right []           = refl
∙s-unit-right (s `, t)     = cong₂ _`,_ (∙s-unit-right s) (substTm-pres-ids t)

module AdhocLemmas where

  --
  keepFreshLemma : {w : Γ ⊆ Γ'} {t : Tm Γ a}
    → wkTm freshWk[ Γ' , b ] (wkTm w t) ≡ wkTm (keep w) (wkTm freshWk t)
  keepFreshLemma = trans
    (trans
      (sym (wkTm-pres-⊆-trans _ _ _))
      (cong₂ wkTm (cong drop (trans (⊆-trans-unit-right _) (sym (⊆-trans-unit-left _)))) refl))
    (wkTm-pres-⊆-trans _ _ _) 

  --
  red-fun-crunch-lemma : (w  : Γ ⊆ Δ) (u : Tm Γ a) (t : Tm (Γ `, a) b)
    → substTm (ids `, wkTm w u) (wkTm (keep w) t) ≡ wkTm w (substTm (ids `, u) t)
  red-fun-crunch-lemma w u t = trans
    (sym (assoc-substTm-wkTm t _ (keep w)))
    (sym (trans
      (sym (substTm-nat t _ _))
      (cong
        (λ p → substTm (p `, wkTm w u) t)
        (sym (trans (trimSub-unit-right w) (sym (wkSub-unit-right w)))))))

  --
  ass-dia-crunch-lemma : (w : Γ ⊆ Γ') (u' : Tm (Γ `, b) (𝕞 c))
    → wkTm (keep freshWk[ Γ' , a ]) (wkTm (keep w) u') ≡ wkTm (keep (keep w)) (wkTm (keep freshWk[ Γ , a ]) u')
  ass-dia-crunch-lemma w u' = trans
    (sym (wkTm-pres-⊆-trans _ _ _))
    (trans
      (cong₂ wkTm (cong (λ z → keep (drop z)) (⊆-trans-unit-right _)) refl)
      (sym (trans
        (sym (wkTm-pres-⊆-trans _ _ _))
        (cong₂ wkTm (cong (λ z → keep (drop z)) (⊆-trans-unit-left _)) refl))))

  --
  letin-collecAcc-crunch-lemma : (w : (Γ `, c) ⊆ Δ) (t : Tm Δ a) (u : Tm (Γ `, a) b)
    → substTm (embWk w `, t) (wkTm (keep freshWk) u) ≡ substTm (embWk (freshWk ∙ w) `, t) u
  letin-collecAcc-crunch-lemma w t u = let open ≡-Reasoning in begin
      substTm (embWk w `, t) (wkTm (keep freshWk) u)
        ≡˘⟨ assoc-substTm-wkTm u (embWk w `, t) (keep freshWk) ⟩
      substTm (trimSub (keep freshWk) (embWk w `, t)) u
        ≡˘⟨ cong (λ z → substTm (trimSub (keep freshWk) (z `, t)) u) (wkSub-unit-right w) ⟩
      substTm (trimSub (keep freshWk) (wkSub w ids `, t)) u
        ≡⟨⟩
      substTm (trimSub ⊆-refl (wkSub w (wkSub freshWk ids) `, t)) u
        ≡⟨ cong (λ z → substTm (z `, t) u) (trimSub-unit-left _) ⟩
      substTm ((wkSub w (wkSub freshWk ids) `, t)) u
        ≡˘⟨ cong (λ z → substTm (z `, t) u) (wkSub-pres-⊆-trans freshWk w ids)  ⟩
      substTm (wkSub (freshWk ∙ w) ids `, t) u
        ≡⟨ cong (λ z → substTm (z `, t) u) (wkSub-unit-right (freshWk ∙ w)) ⟩
      substTm (embWk (freshWk ∙ w) `, t) u ∎

  --
  red-ass-dia-crunch-lemma : (w : Γ ⊆ Θ) (s : Sub Γ Δ) (t : Tm Θ a)
    → wkSub freshWk s ∙s (embWk w `, t) ≡ wkSub w s
  red-ass-dia-crunch-lemma w s t = let open ≡-Reasoning in begin
    wkSub freshWk s ∙s (embWk w `, t)
      ≡˘⟨ assoc-wkSub-∙s s (embWk w `, t) freshWk ⟩
    s ∙s trimSub freshWk (embWk w `, t)
      ≡⟨⟩
    s ∙s trimSub ⊆-refl (embWk w)
      ≡⟨ cong (s ∙s_) (trimSub-unit-left (embWk w)) ⟩
    s ∙s embWk w
      ≡˘⟨ cong (s ∙s_) (wkSub-unit-right w) ⟩
    s ∙s wkSub w ids
      ≡˘⟨ assoc-∙s-wkSub s ids w ⟩
    wkSub w (s ∙s ids)
      ≡⟨ cong (wkSub w) (∙s-unit-right s) ⟩
    wkSub w s ∎
