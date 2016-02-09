module BasicSystem.StructuralNormaliser where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.BigStepSemantics

mutual
  eval : ∀ {Γ Δ α}(t : Tm Δ α)(vs : Env Γ Δ){v : Val Γ α} →
         eval t & vs ⇓ v → Σ (Val Γ α) λ v' → v ≡ v'
  eval .(ƛ t) vs       (rlam {t = t})                 = lam t vs , refl  
  eval .ø .(v ∷ _) (rvar {v = v})        = v , refl  
  eval .(t [ ts ]) vs  (rsubs {t = t}{ts = ts} p p')  with evalˢ ts vs p
  ... | ws , refl = eval t ws p'
  eval .(t ∙ u) vs     (rapp {t = t}{u = u} p p' p'') with eval t vs p | eval u vs p'
  ... | f , refl | a , refl = f ∙∙ a & p''

  _∙∙_&_ : ∀ {Γ α β}(f : Val Γ (α ⇒ β))(a : Val Γ α){v : Val Γ β} →
           f ∙∙ a ⇓ v → Σ (Val Γ β) λ v' → v ≡ v'
  .(lam t vs) ∙∙ a & r∙lam {t = t}{vs = vs} p = eval t (a ∷ vs) p  
  .(ne n)   ∙∙ a & r∙ne {n = n}             = ne (app n a) , refl  

  evalˢ : ∀ {B Γ Δ}(ts : Sub Γ Δ)(vs : Env B Γ){ws : Env B Δ} →
          evalˢ ts & vs ⇓ ws → Σ (Env B Δ) λ ws' → ws ≡ ws'
  evalˢ .↑  .(v ∷ vs) (rˢ↑ {vs = vs}{v = v})         = vs , refl  
  evalˢ .(t ∷ ts)  vs        (rˢcons {ts = ts}{t = t} p p') with evalˢ ts vs p | eval t vs p'
  ... | ws , refl | w , refl = (w ∷ ws) , refl 
  evalˢ .ı        vs        rˢid                             = vs , refl 
  evalˢ .(ts ○ us) vs        (rˢcomp {ts = ts}{us = us} p p') with evalˢ us vs p
  ... | ws , refl = evalˢ ts ws p' 

mutual
  quot : ∀ {Γ α}(v : Val Γ α){n : Nf Γ α} → 
          quot v ⇓ n → Σ (Nf Γ α) λ n' → n ≡ n'
  quot f        (qarr p p')       with val≤ wk f ∙∙ ne (var zero) & p
  ... | v , refl with quot v p' 
  ... | n , refl = lam n , refl 
  quot .(ne m) (qbase {m = m} p) with quotⁿ m p
  ... | n , refl = ne n , refl 

  quotⁿ : ∀ {Γ α}(n : NeVal Γ α){n' : NeNf Γ α} → 
          quotⁿ n ⇓ n' → Σ (NeNf Γ α) λ n'' → n' ≡ n''
  quotⁿ .(var x)   (qⁿvar {x = x})             = var x , refl 
  quotⁿ .(app m v) (qⁿapp {m = m}{v = v} p p') with quotⁿ m p | quot v p'
  ... | n , refl | n' , refl = app n n' , refl

nf : ∀ {Γ α}(t : Tm Γ α){n : Nf Γ α} →
     nf t ⇓ n → Σ (Nf Γ α) λ n' → n ≡ n'
nf t (norm⇓ p p') with eval t id-env p 
... | v , refl = quot v p'

