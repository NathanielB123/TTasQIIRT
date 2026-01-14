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

elimTyOf' : (t : Tm Γ) → Ford (tyOf t)
          → tyOf∙ (elimTm t) ≡ elimTy (tyOf t)

elimTyOf : (t : Tm Γ) → Ford (tyOf t) → (p : tyOf t ≡ A)
  →  tyOf∙ (elimTm t) ≡Ty[ p ] elimTy A
elimTyOf {A = A} t ℱ p = beginTy
  tyOf∙ (elimTm t)
    ≡Ty[]⟨ elimTyOf' t ℱ ⟩
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
  (βπ₂∙ (elimSub σ) (elimTm t) p (elimTyOf {A = A [ σ ]} t ford p) q) 
    (beginTy
    elimTy A [ π₁∙ (elimSub σ , elimTm t ∶[ p , elimTyOf {A = A [ σ ]} t ford p ]∙) ]T∙
      ≡Ty[ cong (A [_]) (βπ₁ σ t p) ]⟨ (λ i → (elimTy A)
        [ βπ₁∙ (elimSub σ) (elimTm t) p (elimTyOf {A = A [ σ ]} t ford p) i ]T∙) ⟩
    elimTy A [ elimSub σ ]T∙
      ≡Ty[ sym p ]⟨ (symP $ elimTyOf {A = A [ σ ]} t ford p) ⟩
    tyOf∙ (elimTm t)
    ∎)
  ) i
elimTm ([idS]t t i)    = [idS]t∙ (elimTm t) i
elimTm ([∘]t t σ τ i)  = [∘]t∙ (elimTm t) (elimSub σ) (elimSub τ) i
elimTm {Γ = Γ} (Tm-is-set≡ t u p q i j) =
  isSet→SquareP
    (λ i j → Tm∙-is-set (elimCtx Γ) (Tm-is-set≡ t u p q i j))
    (λ j → elimTm (p j))
    (λ j → elimTm (q j))
    (λ j → elimTm t)
    (λ j → elimTm u) i j

elimSub ∅              = ∅S∙
elimSub {Γ = Γ} {Δ = Δ} (σ , t ∶[ p ]) =
  elimSub σ , elimTm t ∶[ p , elimTyOf {A = _ [ σ ]} t ford p ]∙
elimSub idS            = idS∙ 
elimSub (σ ∘ τ)       = elimSub σ ∘∙ elimSub τ
elimSub (π₁ σ)        = π₁∙ (elimSub σ)
elimSub (βπ₁≡ σ t p i) 
  = βπ₁∙ (elimSub σ) (elimTm t) p (elimTyOf {A = _ [ σ ]} t ford p) i
elimSub ((idS∘ σ) i)  = (idS∘∙ elimSub σ) i
elimSub ((σ ∘idS) i)  = (elimSub σ ∘idS∙) i
elimSub (assocS σ τ γ i) = assocS∙ (elimSub σ) (elimSub τ) (elimSub γ) i
elimSub (,∘≡ {A} σ t τ p q i) =
  ,∘∙ {A = A} {A∙ = elimTy A} (elimSub σ) (elimTm t) (elimSub τ) p 
      (elimTyOf {A = _ [ σ ]} t ford p) q 
      -- Inlining 'elimTyOf' here helps to ensure termination
      -- (elimTyOf {A = A [ σ ∘ τ ]} (t [ τ ]t) ford q)
      (beginTy
      tyOf∙ (elimTm t [ elimSub τ ]t∙)
        ≡Ty[]⟨ elimTyOf' (t [ τ ]t) ford ⟩
      elimTy (tyOf t) [ elimSub τ ]T∙
        ≡Ty[ q ]⟨ cong elimTy q ⟩
      elimTy A [ elimSub σ ∘∙ elimSub τ ]T∙
        ∎) 
      i

elimSub (η∅ σ i) = η∅∙ (elimSub σ) i
elimSub (ηπℱ' {Γ} {Δ} {A} σ ford (ford {x = .(A [ π₁ σ ])}) ford ford i)
  -- Note: If we remove all the |{Δ = Δ , A}|s in this clause or replace them 
  -- with  |{Δ = Δ Foo., A}|s we get a termination error. 
  -- I think the root issue is
  -- https://github.com/agda/agda/blob/348b95658c8105a0d88510be5ddcd81b16bae36d/src/full/Agda/Termination/TermCheck.hs#L1371
  = let elimTyOf-π₂ : tyOf∙ (elimTm (π₂ σ)) ≡ elimTy A [ π₁∙ (elimSub σ) ]T∙
        elimTyOf-π₂ = beginTy[ refl ]
          tyOf∙ (elimTm (π₂ σ))
            ≡Ty[]⟨ tyOfπ₂∙ (elimSub {Δ = Δ , A} σ) ⟩
          elimTy A [ π₁∙ (elimSub {Δ = Δ , A} σ) ]T∙
            ∎

        elimTyOf-refl : tyOf∙ (elimTm (π₂ σ)) ≡ elimTy A [ elimSub (π₁ σ) ]T∙
        elimTyOf-refl = beginTy
          tyOf∙ (elimTm (π₂ σ))
            ≡Ty[]⟨ elimTyOf-π₂ ⟩
          elimTy A [ elimSub (π₁ σ) ]T∙
            ≡Ty[ refl ]⟨ refl ⟩
          elimTy A [ elimSub (π₁ σ) ]T∙
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
          elimSub (π₁ σ) , elimTm (π₂ σ) ∶[ tyOfπ₂ σ , elimTyOf-refl ]∙ ∎
    in go i
elimSub (Sub-is-set {Γ = Γ} {Δ = Δ} σ τ p q i j) =
  isSet→SquareP
    (λ i j → Sub∙-is-set (elimCtx Γ) (elimCtx Δ) (Sub-is-set σ τ p q i j))
    (λ j → elimSub (p j))
    (λ j → elimSub (q j))
    (λ j → elimSub σ)
    (λ j → elimSub τ) i j

elimTyOf' {Γ} (t [ σ ]t) ford = beginTy
  tyOf∙ (elimTm t [ elimSub σ ]t∙)
    ≡Ty[]⟨ tyOf[]∙ ⟩
  tyOf∙ (elimTm t) [ elimSub σ ]T∙
    ≡Ty[]⟨ (λ i → elimTyOf' t ford i [ elimSub σ ]T∙) ⟩
  elimTy (tyOf t) [ elimSub σ ]T∙
    ∎

elimTyOf' (π₂ {A = B} σ) ford = beginTy
  tyOf∙ (elimTm (π₂ σ))
    ≡Ty[]⟨ tyOfπ₂∙ (elimSub σ) ⟩
  elimTy B [ π₁∙ (elimSub σ) ]T∙
    ∎
elimTyOf' {Γ} (βπ₂≡ {A} σ t p q i) ford
  = let elimTm-βπ₂≡ 
          = (beginTm[ βπ₂ σ t p q ]
              (βπ₂∙ (elimSub σ) (elimTm t) p (elimTyOf {A = A [ σ ]} t ford p) q) 
                (beginTy
                elimTy A [ π₁∙ (elimSub σ , elimTm t ∶[ p , elimTyOf {A = A [ σ ]} t ford p ]∙) ]T∙
                  ≡Ty[ cong (A [_]) (βπ₁ σ t p) ]⟨ (λ i → (elimTy A)
                    [ βπ₁∙ (elimSub σ) (elimTm t) p (elimTyOf {A = A [ σ ]} t ford p) i ]T∙) ⟩
                elimTy A [ elimSub σ ]T∙
                  ≡Ty[ sym p ]⟨ (symP $ elimTyOf {A = A [ σ ]} t ford p) ⟩
                tyOf∙ (elimTm t)
                ∎)
              )

    in  isProp→PathP {B = λ i → tyOf∙ (elimTm-βπ₂≡ i) ≡ elimTy (q i)}  
          (λ j → Ty∙-is-set (elimCtx Γ) _ _ _)
          (elimTyOf' (π₂ (σ Foo., t ∶[ p ])) (ford {x = A [ Foo.π₁ (σ Foo., t ∶[ p ]) ]}))
          (elimTyOf' t ford)
          i
elimTyOf' {Γ} ([idS]t t i) ford = {!!}
  -- = isProp→PathP {B = λ i → tyOf∙ (elimTm ([idS]t t i)) ≡ elimTy ([idS]T i)}  
  --     (λ j → Ty∙-is-set (elimCtx Γ) _ _ _)
  --     (elimTyOf' ([idS]t t i0) ford) (elimTyOf' ([idS]t t i1) ford) i
elimTyOf' {Γ} ([∘]t t σ τ i) ford = {!!}
  -- = isProp→PathP {B = λ i → tyOf∙ (elimTm ([∘]t t σ τ i)) 
  --                         ≡ elimTy ([∘]T (tyOf t) σ τ i)}  
  --     (λ j → Ty∙-is-set (elimCtx Γ) _ _ _)
  --     (elimTyOf' ([∘]t t σ τ i0) ford) (elimTyOf' ([∘]t t σ τ i1) ford) i
elimTyOf' {Γ} (Tm-is-set≡ t u p q i j) ford
  = {!!}
-- elimTyOf' {Γ} (Tm-is-set≡ t u p q i j) ford
--   = let elimTm-is-set = isSet→SquareP
--           (λ i j → Tm∙-is-set (elimCtx Γ) (Tm-is-set≡ t u p q i j))
--           (λ j → elimTm (p j))
--           (λ j → elimTm (q j))
--           (λ j → elimTm t)
--           (λ j → elimTm u)
        
--         tyOf-is-set = 
--           Ty-is-set (tyOf t) (tyOf u) (λ i → tyOf (p i)) (λ i → tyOf (q i))

--         elimTy-is-set : ∀ i j → Ty∙ (elimCtx Γ) (tyOf-is-set i j)
--         elimTy-is-set = λ i j → elimTy {Γ = Γ} (Ty-is-set (tyOf t) (tyOf u) (λ i → tyOf (p i)) (λ i → tyOf (q i)) i j)
--         -- elimTy-is-set = isSet→SquareP
--         --   (λ i j → Ty∙-is-set (elimCtx Γ) 
--         --     (Ty-is-set (tyOf t) (tyOf u) 
--         --                (λ i → tyOf (p i)) (λ i → tyOf (q i)) i j))
--         --   -- These cases are quite problematic
--         --   -- We can make |tyOf t| smaller than |Tm-is-set≡ t u p q i j| with
--         --   -- fording relatively easily, but it is less clear how to make 
--         --   -- |(cong tyOf p) j′| smaller than |Tm-is-set≡ t u p q i j|
--         --   (λ j → elimTy ((cong-noinline tyOf p) j))
--         --   (λ j → elimTy ((cong-noinline tyOf q) j))
--         --   (λ j → elimTy (tyOf t))
--         --   (λ j → elimTy (tyOf u))

  
--         go = isSet→SquareP {A = λ i j → tyOf∙ (elimTm-is-set i j) 
--                                       ≡ elimTy-is-set i j}
--           (λ i j → isProp→isSet (isOfHLevelPathP' {A = λ i → Ty∙ (elimCtx Γ) _} 1 
--                                 (Ty∙-is-set (elimCtx Γ) _) _ _)) 
--           (λ j → elimTyOf' (p j) ford) (λ j → elimTyOf' (q j) ford)
--           (λ j → elimTyOf' t ford) (λ j → elimTyOf' u ford)
--     in (go i j)
