{-# OPTIONS --safe --without-K #-}

import Type
module SMLC.Term.Conversion (𝕤 : Type.Ty) where

open import SMLC.Term.Base 𝕤
open import SMLC.Term.Properties 𝕤

open import Relation.Binary
  using (Setoid ; IsEquivalence)
open import Relation.Binary.Construct.Closure.Equivalence
  using (setoid)
import Relation.Binary.Construct.Closure.Equivalence.Properties
  as EquivalenceProperties

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)

import Relation.Binary.Reasoning.Setoid as EqReasoning

data _≈_ : Tm Γ a → Tm Γ a → Set where

  red-fun : (t : Tm (Γ `, a) b) (u : Tm Γ a)
    → app (lam t) u ≈ substTm (ids `, u) t

  exp-fun : (t : Tm Γ (a ⇒ b))
    → t ≈ lam (app (wkTm freshWk t) (var zero))
    
  red-dia : (t : Tm Γ a)  (u : Tm (Γ `, a) (𝕞 b))
    → letin (return t) u ≈ substTm (ids `, t) u

  exp-dia : (t : Tm Γ (𝕞 a))
    → t ≈ letin t (return (var zero))

  ass-dia : (t : Tm Γ (𝕞 a)) (u : Tm (Γ `, a) (𝕞 b)) (u' : Tm (Γ `, b) (𝕞 c))
    → letin (letin t u) u' ≈ letin t (letin u (wkTm (keep freshWk) u'))

  alg-gp : (t : Tm Γ (𝕞 a))
    → t ≈ get (put (var zero) (wkTm freshWk t))
  
  alg-pp : (t : Tm Γ 𝕤) (t' : Tm Γ 𝕤) (u : Tm Γ (𝕞 a))
    → put t (put t' u) ≈ put t' u

  alg-pg : (t : Tm Γ 𝕤) (u : Tm (Γ `,  𝕤) (𝕞 a))
    → put t (get u) ≈ put t (substTm (ids `, t) u)

  alg-get : (t : Tm (Γ `,  𝕤) (𝕞 a)) (u : Tm (Γ `, a) (𝕞 b))
    → letin (get t) u ≈ get (letin t (wkTm (keep freshWk) u))

  alg-put : (t : Tm Γ 𝕤) (u : Tm Γ (𝕞 a)) (u' : Tm (Γ `, a) (𝕞 b))
    → letin (put t u) u' ≈ put t (letin u u')

  cong-lam : {t t' : Tm (Γ `, a) b}
    → t ≈ t'
    → lam t ≈ lam t'

  cong-app1 : {t t' : Tm Γ (a ⇒ b)} {u : Tm Γ a}
    → t ≈ t'
    → app t u ≈ app t' u

  cong-app2 : {t : Tm Γ (a ⇒ b)} {u u' : Tm Γ a}
    → u ≈ u'
    → app t u ≈ app t u'

  cong-return : {t t' : Tm Γ a}
    → t ≈ t'
    → return t ≈ return t'
    
  cong-letin1 : {t t' : Tm Γ (𝕞 a)} {u : Tm (Γ `, a) (𝕞 b)}
    → t ≈ t'
    → letin t u ≈ letin t' u

  cong-letin2 : {t : Tm Γ (𝕞 a)} {u u' : Tm (Γ `, a) (𝕞 b)}
    → u ≈ u'
    → letin t u ≈ letin t u'

  cong-get : {t t' : Tm (Γ `, 𝕤) (𝕞 a)} 
    → t ≈ t'
    → get t ≈ get t'
    
  cong-put : {t t' : Tm Γ 𝕤} {u : Tm Γ (𝕞 a)}
    → t ≈ t'
    → u ≈ u'
    → put t u ≈ put t' u
    
  ≈-refl : {t : Tm Γ a}
    → t ≈ t

  ≈-sym : {t u : Tm Γ a}
    → t ≈ u → u ≈ t

  ≈-trans : {t u u' : Tm Γ a}
    → t ≈ u → u ≈ u' → t ≈ u'

≈-is-equiv : IsEquivalence (_≈_ {Γ} {a})
≈-is-equiv = record
    { refl  = ≈-refl
    ; sym   = ≈-sym
    ; trans = ≈-trans
    }

Tm-setoid : (Γ : Ctx) → (a : Ty) → Setoid _ _
Tm-setoid Γ a = record
  { Carrier       = Tm Γ a
  ; _≈_           = _≈_
  ; isEquivalence = ≈-is-equiv
  }

≡-to-≈ : ∀ {t u : Tm Γ a} → t ≡ u → t ≈ u
≡-to-≈ ≡-refl = ≈-refl

cong-app≈≡ : ∀ (t≈t' : t ≈ t') (u≡u' : u ≡ u') → app t u ≈ app t' u
cong-app≈≡ t≈t' ≡-refl = cong-app1 t≈t'

cong-app1≈ : ∀ (t≈t' : t ≈ t') → app t u ≈ app t' u
cong-app1≈ t≈t' = cong-app≈≡ t≈t' ≡-refl

cong-app≡≈ : ∀ (t≡t' : t ≡ t') (u≈u' : u ≈ u') → app t u ≈ app t' u'
cong-app≡≈ ≡-refl u≈u' = cong-app2 u≈u'

cong-app2≈ : ∀ (u≈u' : u ≈ u') → app t u ≈ app t u'
cong-app2≈ u≈u' = cong-app≡≈ ≡-refl u≈u'

cong-app≈ : ∀ (t≈t' : t ≈ t') (u≈u' : u ≈ u') → app t u ≈ app t' u'
cong-app≈ t≈t' u≈u' = ≈-trans (cong-app1≈ t≈t') (cong-app2≈ u≈u')

cong-letin : {t t' : Tm Γ (𝕞 a)} {u : Tm (Γ `, a) (𝕞 b)}
    → t ≈ t' → u ≈ u' → letin t u ≈ letin t' u'
cong-letin t≈t' u≈u' = ≈-trans (cong-letin1 t≈t') (cong-letin2 u≈u')


--
-- Derived equations
--

--
-- Derived lemmas for proving the fundamental theorem
--

open AdhocLemmas

wkTm-pres-≈ : (w : Γ ⊆ Γ') {t t' : Tm Γ a} → t ≈ t' → wkTm w t ≈ wkTm w t'
wkTm-pres-≈ w (red-fun t u)         = ≈-trans (red-fun _ _) (≡-to-≈ (red-fun-crunch-lemma w u t))
wkTm-pres-≈ w (exp-fun _)           = ≈-trans (exp-fun _) (≡-to-≈ (cong lam (cong₂ app keepFreshLemma ≡-refl)))
wkTm-pres-≈ w (red-dia t u)         = ≈-trans (red-dia _ _) (≡-to-≈ (red-fun-crunch-lemma w t u))
wkTm-pres-≈ w (ass-dia t u u')      = ≈-trans (ass-dia _ _ _) (cong-letin2 (cong-letin2 (≡-to-≈ (ass-dia-crunch-lemma w u'))))
wkTm-pres-≈ w (exp-dia _)           = exp-dia (wkTm w _)
wkTm-pres-≈ w (cong-lam t≈t')       = cong-lam (wkTm-pres-≈ (_⊆_.keep w) t≈t')
wkTm-pres-≈ w (cong-app1 t≈t')      = cong-app1 (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (cong-app2 t≈t')      = cong-app2 (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (cong-return t≈t')    = cong-return (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (cong-letin1 t≈t')    = cong-letin1 (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (cong-letin2 t≈t')    = cong-letin2 (wkTm-pres-≈ (_⊆_.keep w) t≈t')
wkTm-pres-≈ w ≈-refl                = ≈-refl
wkTm-pres-≈ w (≈-sym t≈t')          = ≈-sym (wkTm-pres-≈ w t≈t')
wkTm-pres-≈ w (≈-trans t≈t' t'≈t'') = ≈-trans (wkTm-pres-≈ w t≈t') (wkTm-pres-≈ w t'≈t'')
wkTm-pres-≈ w (alg-gp _)            = ≈-trans (alg-gp _) (cong-get (≡-to-≈ (cong (put (var zero)) keepFreshLemma)))
wkTm-pres-≈ w (alg-pp t t' u)       = alg-pp (wkTm w t) (wkTm w t') (wkTm w u)
wkTm-pres-≈ w (alg-pg t u)          = ≈-trans (alg-pg _ _) (≡-to-≈ (cong (put _) (red-fun-crunch-lemma w t u)))
wkTm-pres-≈ w (alg-get t u)         = ≈-trans (alg-get _ _) (≡-to-≈ (cong get (cong (letin _) (ass-dia-crunch-lemma w u))))
wkTm-pres-≈ w (alg-put t u u')      = alg-put (wkTm w t) (wkTm w u) (wkTm (keep w) u')
wkTm-pres-≈ w (cong-get t≈t')       = cong-get (wkTm-pres-≈ (keep w) t≈t')
wkTm-pres-≈ w (cong-put t≈t' t≈t'') = cong-put (wkTm-pres-≈ w t≈t') ≈-refl

red-fun-tr-lemma : (w : Γ ⊆ Γ') (s : Sub Γ Δ) (t : Tm (Δ `, a) b) (u : Tm Γ' a)
  → app (wkTm w (substTm s (lam t))) u ≈ substTm (wkSub w s `, u) t
red-fun-tr-lemma w s t u = let open EqReasoning (Tm-setoid _ _) in begin
    -- normalize
  app (lam (wkTm (keep w) (substTm (keeps s) t))) u
    ≈⟨ red-fun _ u  ⟩
  substTm (ids `, u) (wkTm (keep w) (substTm (keeps s) t))
    ≡˘⟨ cong (substTm (ids `, u)) (substTm-nat t (keeps s) (keep w)) ⟩
  substTm (ids `, u) (substTm (wkSub (keep w) (keeps s)) t)
    ≡˘⟨ substTm-pres-∙s _ _ t ⟩
  substTm (wkSub (keep w) (keeps s) ∙s (ids `, u)) t
    ≡˘⟨ cong (λ s' → substTm ((s' ∙s _) `, u) t) (wkSub-pres-⊆-trans _ _ _) ⟩
  substTm ((wkSub (freshWk ∙ keep w) s ∙s (ids `, u)) `, u) t
    ≡⟨ cong (λ s' → substTm (s' `, u) t) (cong (_∙s _) (cong₂ wkSub (cong drop (⊆-trans-unit-left w)) ≡-refl)) ⟩
  substTm ((wkSub (drop w) s ∙s (ids `, u)) `, u) t
    ≡˘⟨ cong (λ s' → substTm (s' `, u) t) (assoc-wkSub-∙s _ _ _) ⟩
    -- normalize
  substTm ((s ∙s trimSub w ids) `, u) t
    ≡⟨ cong (λ s' → substTm ((s ∙s s') `, u) t) (trimSub-unit-right w) ⟩
  substTm ((s ∙s embWk w) `, u) t
    ≡˘⟨ cong (λ s' → substTm (s' `, u) t) (cong (s ∙s_) (wkSub-unit-right w)) ⟩
  substTm ((s ∙s wkSub w ids) `, u) t
    ≡˘⟨ cong (λ s' → substTm (s' `, u) t) (assoc-∙s-wkSub _ _ _) ⟩
  substTm (wkSub w (s ∙s ids) `, u) t
    ≡⟨ cong (λ s' → substTm (s' `, u) t) (cong (wkSub w) (∙s-unit-right s)) ⟩
  substTm (wkSub w s `, u) t ∎   
