module BasicSystem.StructuralNormaliser where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.BigStepSemantics

mutual
  eval : ∀ {Γ Δ σ}(t : Tm Δ σ)(vs : Env Γ Δ){v : Val Γ σ} →
         eval t & vs ⇓ v → Σ (Val Γ σ) λ v' → v ≡ v'
  eval .(ƛ t) vs       (rlam {t = t})                 = λv t vs , refl  
  eval .ø .(_ << v) (rvar {v = v})        = v , refl  
  eval .(t [ ts ]) vs  (rsubs {t = t}{ts = ts} p p')  with evalˢ ts vs p
  ... | ws , refl = eval t ws p'
  eval .(t ∙ u) vs     (rapp {t = t}{u = u} p p' p'') with eval t vs p | eval u vs p'
  ... | f , refl | a , refl = f ∙∙ a & p''

  _∙∙_&_ : ∀ {Γ σ τ}(f : Val Γ (σ ⇒ τ))(a : Val Γ σ){v : Val Γ τ} →
           f ∙∙ a ⇓ v → Σ (Val Γ τ) λ v' → v ≡ v'
  .(λv t vs) ∙∙ a & r∙lam {t = t}{vs = vs} p = eval t (vs << a) p  
  .(nev n)   ∙∙ a & r∙ne {n = n}             = nev (appV n a) , refl  

  evalˢ : ∀ {B Γ Δ}(ts : Sub Γ Δ)(vs : Env B Γ){ws : Env B Δ} →
          evalˢ ts & vs ⇓ ws → Σ (Env B Δ) λ ws' → ws ≡ ws'
  evalˢ .(↑ _)  .(vs << v) (rˢ↑ {vs = vs}{v = v})         = vs , refl  
  evalˢ .(ts < t)  vs        (rˢcons {ts = ts}{t = t} p p') with evalˢ ts vs p | eval t vs p'
  ... | ws , refl | w , refl = (ws << w) , refl 
  evalˢ .ı        vs        rˢid                             = vs , refl 
  evalˢ .(ts ○ us) vs        (rˢcomp {ts = ts}{us = us} p p') with evalˢ us vs p
  ... | ws , refl = evalˢ ts ws p' 

mutual
  quot : ∀ {Γ σ}(v : Val Γ σ){n : Nf Γ σ} → 
          quot v ⇓ n → Σ (Nf Γ σ) λ n' → n ≡ n'
  quot f        (qarr p p')       with vwk _ f ∙∙ nev (varV vZ) & p
  ... | v , refl with quot v p' 
  ... | n , refl = λn n , refl 
  quot .(nev m) (qbase {m = m} p) with quotⁿ m p
  ... | n , refl = ne n , refl 

  quotⁿ : ∀ {Γ σ}(n : NeV Γ σ){n' : NeN Γ σ} → 
          quotⁿ n ⇓ n' → Σ (NeN Γ σ) λ n'' → n' ≡ n''
  quotⁿ .(varV x)   (qⁿvar {x = x})             = varN x , refl 
  quotⁿ .(appV m v) (qⁿapp {m = m}{v = v} p p') with quotⁿ m p | quot v p'
  ... | n , refl | n' , refl = appN n n' , refl

open import BasicSystem.IdentityEnvironment

nf : ∀ {Γ σ}(t : Tm Γ σ){n : Nf Γ σ} →
     nf t ⇓ n → Σ (Nf Γ σ) λ n' → n ≡ n'
nf t (norm⇓ p p') with eval t vid p 
... | v , refl = quot v p'

