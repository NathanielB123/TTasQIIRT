{-# OPTIONS --hidden-argument-puns --no-require-unique-meta-solutions #-} --show-implicit 
open import Prelude

open import Theory.SC.QIIRT-tyOf.IxModel

module Theory.SC.QIIRT-tyOf.Elim (C∙ : SC∙ ℓ₁ ℓ₂ ℓ₃ ℓ₄) where

private
  module M = SC∙ C∙
open M hiding (module Var)
open M.Var

open import Theory.SC.QIIRT-tyOf.Syntax
open Var

-- {-# TERMINATING #-}
elimCtx  : (Γ : Ctx) → Ctx∙ Γ
elimTy   : (A : Ty Γ) → Ty∙ (elimCtx Γ) A
elimTm   : (t : Tm Γ) → Tm∙ (elimCtx Γ) t
elimSub  : (σ : Sub Γ Δ) → Sub∙ (elimCtx Γ) (elimCtx Δ) σ

elimTyOf' : (t : Tm Γ) → tyOf∙ (elimTm t) ≡ elimTy (tyOf t)

elimTyOf : (t : Tm Γ) (p : tyOf t ≡ A)
         → tyOf∙ (elimTm t) ≡Ty[ p ] elimTy A
elimTyOf {A = A} t p = beginTy
  tyOf∙ (elimTm t)
    ≡Ty[]⟨ elimTyOf' t ⟩
  elimTy (tyOf t)
    ≡Ty[ p ]⟨ cong elimTy p ⟩
  elimTy A
    ∎

{-# INLINE elimTyOf #-}


elimCtx ∅        = ∅∙
elimCtx (Γ , A)  = elimCtx Γ ,∙ elimTy A

elimTy (A [ σ ]) = elimTy A [ elimSub σ ]T∙
elimTy U         = U∙
elimTy ([idS]T {A} i) = [idS]T∙ (elimTy A) i
elimTy ([∘]T A σ τ i) = [∘]T∙ (elimTy A) (elimSub σ) (elimSub τ) i
elimTy (U[] {σ} i) = U[]∙ {σ∙ = elimSub σ} i
elimTy {Γ = Γ} (Ty-is-set A B p q i j) =
  isSet→SquareP
    (λ i j → Ty∙-is-set (elimCtx Γ) (Ty-is-set A B p q i j))
    (λ j → elimTy (p j))
    (λ j → elimTy (q j))
    (λ j → elimTy A)
    (λ j → elimTy B) i j


elimTm (t [ σ ]t) = elimTm t [ elimSub σ ]t∙
elimTm (π₂ σ)    = π₂∙ (elimSub σ)
elimTm (βπ₂≡ {A} σ t p q i) = (beginTm[ βπ₂ σ t p q ]
  (βπ₂∙ (elimSub σ) (elimTm t) p (elimTyOf {A = A [ σ ]} t p) q) 
    (beginTy
    elimTy A [ π₁∙ (elimSub σ , elimTm t ∶[ p , elimTyOf {A = A [ σ ]} t p ]∙) ]T∙
      ≡Ty[ cong (A [_]) (βπ₁ σ t p) ]⟨ (λ i → (elimTy A)
        [ βπ₁∙ (elimSub σ) (elimTm t) p (elimTyOf {A = A [ σ ]} t p) i ]T∙) ⟩
    elimTy A [ elimSub σ ]T∙
      ≡Ty[ sym p ]⟨ (symP $ elimTyOf {A = A [ σ ]} t p) ⟩
    tyOf∙ (elimTm t)
    ∎)
  ) i
elimTm ([idS]t≡ t i)   = [idS]t∙ (elimTm t) i
elimTm ([∘]t≡ t σ τ i)  = [∘]t∙ (elimTm t) (elimSub σ) (elimSub τ) i
elimTm {Γ = Γ} (Tm-is-set≡ t u p q i j) =
  isSet→SquareP
    (λ i j → Tm∙-is-set (elimCtx Γ) (Tm-is-set≡ t u p q i j))
    (λ j → elimTm (p j))
    (λ j → elimTm (q j))
    (λ j → elimTm t)
    (λ j → elimTm u) i j

elimSub ∅              = ∅S∙
elimSub {Γ = Γ} {Δ = Δ} (σ , t ∶[ p ]) =
  elimSub σ , elimTm t ∶[ p , elimTyOf {A = _ [ σ ]} t p ]∙
elimSub idS            = idS∙ 
elimSub (σ ∘ τ)       = elimSub σ ∘∙ elimSub τ
elimSub (π₁ σ)        = π₁∙ (elimSub σ)
elimSub (βπ₁≡ σ t p i) 
  = βπ₁∙ (elimSub σ) (elimTm t) p (elimTyOf {A = _ [ σ ]} t p) i
elimSub ((idS∘ σ) i)  = (idS∘∙ elimSub σ) i
elimSub ((σ ∘idS) i)  = (elimSub σ ∘idS∙) i
elimSub (assocS σ τ γ i) = assocS∙ (elimSub σ) (elimSub τ) (elimSub γ) i
elimSub (,∘≡ {A} σ t τ p q i) =
  ,∘∙ {A = A} {A∙ = elimTy A} (elimSub σ) (elimTm t) (elimSub τ) p 
      (elimTyOf {A = _ [ σ ]} t p) q 
      -- Inlining 'elimTyOf' here helps to ensure termination
      -- (elimTyOf {A = A [ σ ∘ τ ]} (t [ τ ]t) q)
      (beginTy
      tyOf∙ (elimTm t [ elimSub τ ]t∙)
        ≡Ty[]⟨ elimTyOf' (t [ τ ]t) ⟩
      -- Note that |elimTy (tyOf (t [ τ ]t))| fails here. Termination checking
      -- is super brittle!
      -- I think the root cause is
      -- https://github.com/agda/agda/blob/348b95658c8105a0d88510be5ddcd81b16bae36d/src/full/Agda/Termination/TermCheck.hs#L1371
      elimTy (tyOf t) [ elimSub τ ]T∙
        ≡Ty[ q ]⟨ cong elimTy q ⟩
      elimTy A [ elimSub σ ∘∙ elimSub τ ]T∙
        ∎) 
      i

elimSub (η∅ σ i) = η∅∙ (elimSub σ) i
elimSub (ηπ≡ {Γ} {Δ} {A} σ i)
  -- Note: If we remove all the |{Δ = Δ , A}|s in this clause or replace them 
  -- with  |{Δ = Δ Foo., A}|s we get a termination error. 
  -- I think this is
  -- https://github.com/agda/agda/blob/348b95658c8105a0d88510be5ddcd81b16bae36d/src/full/Agda/Termination/TermCheck.hs#L1371
  -- again
  = let elimTyOf-refl : tyOf∙ (elimTm (π₂ σ)) ≡ elimTy (A [ π₁ σ ])
        elimTyOf-refl = beginTy
          tyOf∙ (elimTm (π₂ σ))
            ≡Ty[]⟨ elimTyOf' (π₂ σ) ⟩
          elimTy (A [ π₁ σ ])
            ≡Ty[ refl ]⟨ refl ⟩
          elimTy (A [ π₁ σ ])
            ∎
  
        go : elimSub σ ≡Sub[ ηπ≡ σ ] 
             (elimSub (π₁ σ) , elimTm (π₂ σ) 
              ∶[ tyOfπ₂ σ , elimTyOf-refl ]∙)
        go = beginSub
          elimSub {Δ = Δ , A} σ 
            ≡Sub[ ηπ σ ]⟨ ηπ∙ (elimSub σ) ⟩
          π₁∙ (elimSub {Δ = Δ , A} σ) 
          , π₂∙ (elimSub {Δ = Δ , A} σ) ∶[ refl , tyOfπ₂∙ (elimSub σ) ]∙
            ≡Sub[ refl ]⟨ cong (π₁∙ (elimSub {Δ = Δ , A} σ) 
                        , π₂∙ (elimSub {Δ = Δ , A} σ) ∶[ refl ,_]∙) 
                              (Ty∙-is-set _ _ _ _ _ _) ⟩
          elimSub (π₁ σ) , elimTm (π₂ σ) ∶[ tyOfπ₂ σ , elimTyOf-refl  ]∙ ∎
    in go i
elimSub (Sub-is-set {Γ = Γ} {Δ = Δ} σ τ p q i j) =
  isSet→SquareP
    (λ i j → Sub∙-is-set (elimCtx Γ) (elimCtx Δ) (Sub-is-set σ τ p q i j))
    (λ j → elimSub (p j))
    (λ j → elimSub (q j))
    (λ j → elimSub σ)
    (λ j → elimSub τ) i j

elimTyOf' {Γ} (t [ σ ]t) = beginTy
  tyOf∙ (elimTm t [ elimSub σ ]t∙)
    ≡Ty[]⟨ tyOf[]∙ ⟩
  tyOf∙ (elimTm t) [ elimSub σ ]T∙
    ≡Ty[]⟨ (λ i → elimTyOf' t i [ elimSub σ ]T∙) ⟩
  elimTy (tyOf t) [ elimSub σ ]T∙
    ∎

elimTyOf' (π₂ {A = B} σ) = beginTy
  tyOf∙ (elimTm (π₂ σ))
    ≡Ty[]⟨ tyOfπ₂∙ (elimSub σ) ⟩
  elimTy B [ π₁∙ (elimSub σ) ]T∙
    ∎
elimTyOf' {Γ} (βπ₂≡ {A} σ t p q i)
  = let elimTm-βπ₂≡ 
          = (beginTm[ βπ₂ σ t p q ]
              (βπ₂∙ (elimSub σ) (elimTm t) p (elimTyOf {A = A [ σ ]} t p) q) 
                (beginTy
                elimTy A [ π₁∙ (elimSub σ , elimTm t ∶[ p , elimTyOf {A = A [ σ ]} t p ]∙) ]T∙
                  ≡Ty[ cong (A [_]) (βπ₁ σ t p) ]⟨ (λ i → (elimTy A)
                    [ βπ₁∙ (elimSub σ) (elimTm t) p (elimTyOf {A = A [ σ ]} t p) i ]T∙) ⟩
                elimTy A [ elimSub σ ]T∙
                  ≡Ty[ sym p ]⟨ (symP $ elimTyOf {A = A [ σ ]} t p) ⟩
                tyOf∙ (elimTm t)
                ∎)
              )

    in  isProp→PathP {B = λ i → tyOf∙ (elimTm-βπ₂≡ i) ≡ elimTy (q i)}  
          (λ j → Ty∙-is-set (elimCtx Γ) _ _ _)
          (elimTyOf' (π₂ (σ Foo., t ∶[ p ])))
          (elimTyOf' t)
          i
elimTyOf' {Γ} ([idS]t≡ t i)
  = isProp→PathP {B = λ i → tyOf∙ ([idS]t∙ (elimTm t) i) ≡ [idS]T∙ (elimTy (tyOf t)) i}  
      (λ j → Ty∙-is-set (elimCtx Γ) _ _ _)
      (elimTyOf' t) (elimTyOf' (t [ Foo.idS ]t)) i
elimTyOf' {Γ} ([∘]t≡ t σ τ i)
  = isProp→PathP {B = λ i → tyOf∙ ([∘]t∙ (elimTm t) (elimSub σ) (elimSub τ) i) 
                          ≡ [∘]T∙ (elimTy (tyOf t)) (elimSub σ) (elimSub τ) i}  
      (λ j → Ty∙-is-set (elimCtx Γ) _ _ _)
      (elimTyOf' (t Foo.[ τ ]t [ σ ]t)) 
      (elimTyOf' (t [ τ Foo.∘ σ ]t)) 
      i
elimTyOf' {Γ} (Tm-is-set≡ t u p q i j) 
  = let elimTm-is-set = isSet→SquareP
          (λ i j → Tm∙-is-set (elimCtx Γ) (Tm-is-set≡ t u p q i j))
          (λ j → elimTm (p j))
          (λ j → elimTm (q j))
          (λ j → elimTm t)
          (λ j → elimTm u)
        
        elimTy-is-set = isSet→SquareP
          (λ i j → Ty∙-is-set (elimCtx Γ) 
            (Ty-is-set (tyOf t) (tyOf u) 
                       (λ i → tyOf (p i)) (λ i → tyOf (q i)) i j))
          -- These cases are quite problematic
          -- We can make |tyOf t| smaller than |Tm-is-set≡ t u p q i j| with
          -- fording relatively easily, but it is less clear how to make 
          -- |(cong tyOf p) j′| smaller than |Tm-is-set≡ t u p q i j|
          (λ j → elimTy (tyOf (p j)))
          (λ j → elimTy (tyOf (q j)))
          (λ j → elimTy (tyOf t))
          (λ j → elimTy (tyOf u))

  
        go = isSet→SquareP {A = λ i j → tyOf∙ (elimTm-is-set i j) 
                                      ≡ elimTy-is-set i j}
          (λ i j → isProp→isSet (isOfHLevelPathP' {A = λ i → Ty∙ (elimCtx Γ) _} 1 
                                (Ty∙-is-set (elimCtx Γ) _) _ _)) 
          (λ j → elimTyOf' (p j)) (λ j → elimTyOf' (q j))
          (λ j → elimTyOf' t) (λ j → elimTyOf' u)
    -- The only idea I have for fixing this is do the hcomps manually, but that 
    -- is gonna suck (and I'm not sure it would even help)...
    in {!go i j!} 
