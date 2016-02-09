module BasicSystem.TerminationandCompleteness where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Conversion
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.BigStepSemantics
open import BasicSystem.OPEBigStep
open import BasicSystem.StrongComputability

-- embEnv id-env ≈≈ ı

embEnv∘id-env : ∀ {Γ} → embEnv (id-env {Γ}) ≈≈ ı
embEnv∘id-env {[]} = ≈≈refl
embEnv∘id-env {x ∷ Γ} = begin
  ø ∷ embEnv (env≤ wk id-env)
    ≡⟨⟩
  ø ∷ embEnv (env≤ wk id-env)
    ≈⟨ ≈≈cong∷ ≈refl (embEnv∘≤ wk id-env) ⟩
  ø ∷ embEnv id-env ○ (≤2sub ≤id ○ ↑)
    ≈⟨ ≈≈cong∷ ≈refl (≈≈cong○ ≈≈refl (≈≈cong○ ı≈≈≤2sub-≤id ≈≈refl)) ⟩
  ø ∷ embEnv id-env ○ (ı ○ ↑)
    ≈⟨ ≈≈cong∷ ≈refl (≈≈cong○ embEnv∘id-env ≈≈idl) ⟩
  ø ∷ (ı ○ ↑)
    ≈⟨ ≈≈sym ≈≈id∷ ⟩
  ı
  ∎
  where open ≈≈-Reasoning

mutual
  postulate
    fundthrm : ∀ {Γ Δ α}(t : Tm Δ α)(vs : Env Γ Δ) → SCE vs →
               Σ (Val Γ α) 
                 λ v → eval t & vs ⇓ v × SCV v × (t [ embEnv vs ] ≈ embVal v)
  {-
  fundthrm ø        (v ∷ vs) (s<< svs sv) = v , rvar , sv ,  ≈proj
  fundthrm (t [ ts ]) vs svs = 
     proj₁ sw , 
       rsubs (proj₁ (proj₂ sws)) (proj₁ (proj₂ sw)) ,
         (proj₁ ∘ proj₂) (proj₂ sw) ,
            ≈trans (≈trans (≈sym ≈comp) (≈cong[] ≈refl ((proj₂ ∘ proj₂) (proj₂ sws)))) ((proj₂ ∘ proj₂) (proj₂ sw))
     where
     sws = fundthrmˢ ts vs svs
     sw  = fundthrm t (proj₁ sws) ((proj₁ ∘ proj₂) (proj₂ sws))
  fundthrm (ƛ t)      vs svs = 
    lam t vs ,
        rlam , 
            (λ {_} f a sa → 
              let st = fundthrm t (a ∷ env≤ f vs) (s<< (scenv≤ f vs svs) sa) 
              in  proj₁ st , 
                      r∙lam (proj₁ (proj₂ st)) ,
                          (proj₁ ∘ proj₂) (proj₂ st) ,
                          {!!}
                          {-≈trans 
                            (≈trans 
                              (≈cong∙ ≈lam ≈refl)
                              (≈trans 
                                ≈βσ ?
                                {-(≈trans 
                                  (≈sym ≈comp) 
                                  (≈cong[] 
                                    ≈refl 
                                    (≈≈trans 
                                      ≈≈cons 
                                        (≈≈cong∷ 
                                          (≈≈trans 
                                            ≈≈assoc 
                                            (≈≈trans 
                                              (≈≈cong○ ≈≈refl ≈≈wk) 
                                              ≈≈idr)) 
                                          ≈proj))))
                                          ))
                                  ((proj₂ ∘ proj₂) (proj₂ st)))-} ,
            ≈refl
  fundthrm (t ∙ u)    vs svs = 
    proj₁ stu , 
        rapp (proj₁ (proj₂ st)) 
                  (proj₁ (proj₂ su)) 
                  (helper' (sym (val≤-≤id (proj₁ st))) (proj₁ (proj₂ stu))) ,
            (proj₁ ∘ proj₂) (proj₂ stu) ,
            ≈trans (≈trans ≈app ((≈cong∙ ((proj₂ ∘ proj₂) (proj₂ st)) ((proj₂ ∘ proj₂) (proj₂ su))))) (helper'' (sym (val≤-≤id (proj₁ st))) {(proj₁ (fundthrm u vs svs))}{proj₁ ((proj₁ ∘ proj₂) (proj₂ (fundthrm t vs svs)) ≤id (proj₁ (fundthrm u vs svs)) ((proj₁ ∘ proj₂) (proj₂ (fundthrm u vs svs))))} ((proj₂ ∘ proj₂) (proj₂ stu)))
    where
    st  = fundthrm t vs svs
    su  = fundthrm u vs svs
    stu = (proj₁ ∘ proj₂) (proj₂ st) ≤id (proj₁ su) ((proj₁ ∘ proj₂) (proj₂ su))
  -}-}

  fundthrmˢ : ∀ {B Γ Δ}(ts : Sub Γ Δ)(vs : Env B Γ) → SCE vs →
              Σ (Env B Δ) 
                λ ws → 
                  evalˢ ts & vs ⇓ ws × SCE ws × (ts ○ (embEnv vs) ≈≈ embEnv ws)
  fundthrmˢ ↑ (v ∷ vs) (s<< svs sv) = vs , rˢ↑ , svs , ≈≈wk
  fundthrmˢ (t ∷ ts)  vs        svs          = 
    proj₁ st ∷ proj₁ sts ,
        rˢcons (proj₁ (proj₂ sts)) (proj₁ (proj₂ st)) ,
            s<< ((proj₁ ∘ proj₂) (proj₂ sts)) ((proj₁ ∘ proj₂) (proj₂ st)) ,
            ≈≈trans ≈≈cons (≈≈cong∷ ((proj₂ ∘ proj₂) (proj₂ st)) ((proj₂ ∘ proj₂) (proj₂ sts)))
    where
    sts = fundthrmˢ ts vs svs
    st  = fundthrm  t  vs svs
  fundthrmˢ ı        vs        svs          = vs , rˢid , svs , ≈≈idl
  fundthrmˢ (ts ○ us) vs        svs          = 
    proj₁ sts ,
        rˢcomp (proj₁ (proj₂ sus)) (proj₁ (proj₂ sts)) ,
            (proj₁ ∘ proj₂) (proj₂ sts) ,
            ≈≈trans (≈≈trans ≈≈assoc (≈≈cong○ ≈≈refl ((proj₂ ∘ proj₂) (proj₂ sus)))) ((proj₂ ∘ proj₂) (proj₂ sts))
    where
    sus = fundthrmˢ us vs svs
    sts = fundthrmˢ ts (proj₁ sus) ((proj₁ ∘ proj₂) (proj₂ sus))

mutual
  quotlema : ∀ {Γ} α {v : Val Γ α} → 
              SCV v → Σ (Nf Γ α) (λ m →  quot v ⇓ m × (embVal v ≈ embNf m ))
  quotlema ⋆ {ne n} (m , p , q) = ne m , qbase p , q
  quotlema {Γ} (α ⇒ β) {v} sv =
    lam (proj₁ qvvZ) ,
        (qarr (proj₁ (proj₂ svvZ)) (proj₁ (proj₂ qvvZ))) ,
            (≈trans 
              ≈η 
              (≈congƛ 
                (≈trans 
                  (≈cong∙ 
                    (≈trans
                      (≈trans (≈cong[] (≈trans (≈sym ≈id) (≈cong[] ≈refl
                                       (≈≈sym ı≈≈≤2sub-≤id))) 
                                     ≈≈refl ) 
                             (≈sym ≈comp)) 
                      (≈sym (embVal∘≤ (≤weak ≤id) v))) 
                    ≈refl) 
                  (≈trans ((proj₂ ∘ proj₂) (proj₂ svvZ)) (proj₂ (proj₂ qvvZ))))))
    where
    svZ = quotlemb α {var (zero {Γ = Γ})} qⁿvar ≈refl
    svvZ = sv (≤weak ≤id) (ne (var zero)) svZ
    qvvZ = quotlema β ((proj₁ ∘ proj₂) (proj₂ svvZ))

  quotlemb : ∀ {Γ} α {n : NeVal Γ α}{m : NeNf Γ α} → 
              quotⁿ n ⇓ m → embNeVal n ≈ embNeNf m → SCV (ne n)
  quotlemb ⋆       {n} p q = _ , p , q 
  quotlemb (α ⇒ β) {n}{m} p q = λ f a sa → 
    let qla = quotlema α sa
    in  ne (app (neVal≤ f n) a) ,
            r∙ne ,
                quotlemb β 
                           (qⁿapp (quotⁿ⇓map f p) (proj₁ (proj₂ qla))) 
                           (≈cong∙ (≈trans (embNeVal∘≤ f n) 
                                         (≈trans (≈cong[] q ≈≈refl) 
                                                (≈sym (embNeNf∘≤ f m)))) 
                                  (proj₂ (proj₂ qla))) ,
                ≈cong∙ (≈trans (embNeVal∘≤ f n) (≈sym (embNeVal∘≤ f n))) ≈refl


scvar : ∀ {Γ α}(x : Var Γ α) → SCV (ne (var x))
scvar x = quotlemb _ qⁿvar ≈refl 

scid : ∀ Γ → SCE (id-env {Γ})
scid []       = s[] 
scid (α ∷ Γ) = s<< (scenv≤ wk _ (scid Γ)) (scvar zero) 

postulate
  normthrm : ∀ {Γ α}(t : Tm Γ α) → Σ (Nf Γ α) λ n → nf t ⇓ n × (t ≈ embNf n)
{-normthrm t = proj₁ qt , norm⇓ (proj₁ (proj₂ ft)) (proj₁ (proj₂ qt)) ,
                         ≈trans (≈trans (≈trans (≈sym ≈id) (≈cong[] ≈refl embEnv∘id-env))
                                       ((proj₂ ∘ proj₂) (proj₂ ft))) 
                                (proj₂ (proj₂ qt))
  where
  ft = fundthrm t id-env (scid _)
  qt = quotlema _ ((proj₁ ∘ proj₂) (proj₂ ft))
-}
