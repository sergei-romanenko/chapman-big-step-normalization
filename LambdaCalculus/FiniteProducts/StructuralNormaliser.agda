module FiniteProducts.StructuralNormaliser where
open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.OPE
open import FiniteProducts.BigStepSemantics

mutual
  eval : ∀ {Γ Δ σ}(t : Tm Δ σ)(vs : Env Γ Δ){v : Val Γ σ} →
         eval t & vs ⇓ v → Σ (Val Γ σ) λ v' → v ≡ v'
  eval .top .(_ << v) (rvar {v = v}) = v , refl  
  eval .(t [ ts ]) vs (rsubs {t = t}{ts = ts} p p') with evalˢ ts vs p
  ... | ws , refl = eval t ws p'
  eval .(λt t) vs (rlam {t = t}) = λv t vs , refl  
  eval .(t $ u) vs (rapp {t = t}{u = u} p p' p'') with eval t vs p | eval u vs p'
  ... | f , refl | a , refl = f $$ a & p''
  eval .void vs rvoid = voidv , refl  
  eval .(< t , u >) vs (r<,> {t = t}{u = u} p p') with eval t vs p | eval u vs p'
  ... | v , refl | w , refl = < v , w >v , refl   
  eval .(fst t) vs (rfst {t = t} p p') with eval t vs p
  ... | v , refl = vfst v p' 
  eval .(snd t) vs (rsnd {t = t} p p') with eval t vs p
  ... | v , refl = vsnd v p' 

  vfst : ∀ {Γ σ τ}(v : Val Γ (σ * τ)){w : Val Γ σ} → vfst v ⇓ w →
         Σ (Val Γ σ) λ w' → w ≡ w'
  vfst .(< v , w >v) (rfst<,> {v = v}{w = w}) = v , refl  
  vfst .(nev n)      (rfstnev {n = n})        = nev (fstV n) , refl  

  vsnd : ∀ {Γ σ τ}(v : Val Γ (σ * τ)){w : Val Γ τ} → vsnd v ⇓ w →
         Σ (Val Γ τ) λ w' → w ≡ w'
  vsnd .(< v , w >v) (rsnd<,> {v = v}{w = w}) = w , refl
  vsnd .(nev n)      (rsndnev {n = n})        = nev (sndV n) , refl 

  _$$_&_ : ∀ {Γ σ τ}(f : Val Γ (σ ⇒ τ))(a : Val Γ σ){v : Val Γ τ} →
           f $$ a ⇓ v → Σ (Val Γ τ) λ v' → v ≡ v'
  .(λv t vs) $$ a & r$lam {t = t}{vs = vs} p = eval t (vs << a) p  
  .(nev n)   $$ a & r$ne {n = n}             = nev (appV n a) , refl  

  evalˢ : ∀ {B Γ Δ}(ts : Sub Γ Δ)(vs : Env B Γ){ws : Env B Δ} →
          evalˢ ts & vs ⇓ ws → Σ (Env B Δ) λ ws' → ws ≡ ws'
  evalˢ .(pop _)  .(vs << v) (rˢpop {vs = vs}{v = v})         = vs , refl  
  evalˢ .(ts < t)  vs        (rˢcons {ts = ts}{t = t} p p') with evalˢ ts vs p | eval t vs p'
  ... | ws , refl | w , refl = (ws << w) , refl 
  evalˢ .id        vs        rˢid                             = vs , refl 
  evalˢ .(ts ○ us) vs        (rˢcomp {ts = ts}{us = us} p p') with evalˢ us vs p
  ... | ws , refl = evalˢ ts ws p' 

mutual
  quot : ∀ {Γ σ}(v : Val Γ σ){n : Nf Γ σ} → 
          quot v ⇓ n → Σ (Nf Γ σ) λ n' → n ≡ n'
  quot .(nev m) (qbase {m = m} p) with quotⁿ m p
  ... | n , refl = ne n , refl 
  quot f        (qarr p p')       with vwk _ f $$ nev (varV vZ) & p
  ... | v , refl with quot v p' 
  ... | n , refl = λn n , refl 
  quot _        qone = voidn , refl  
  quot v        (qprod p p' p'' p''') with vfst v p | vsnd v p''
  ... | w , refl | sw' , refl with quot w p' | quot sw' p'''
  ... | x , refl | x' , refl = < x , x' >n , refl  

  quotⁿ : ∀ {Γ σ}(n : NeV Γ σ){n' : NeN Γ σ} → 
          quotⁿ n ⇓ n' → Σ (NeN Γ σ) λ n'' → n' ≡ n''
  quotⁿ .(varV x)   (qⁿvar {x = x})             = varN x , refl 
  quotⁿ .(appV m v) (qⁿapp {m = m}{v = v} p p') with quotⁿ m p | quot v p'
  ... | n , refl | n' , refl = appN n n' , refl
  quotⁿ .(fstV m)   (qⁿfst {m = m} p) with quotⁿ m p
  ... | n , refl = fstN n , refl 
  quotⁿ .(sndV m)   (qⁿsnd {m = m} p) with quotⁿ m p
  ... | n , refl = sndN n , refl 

open import FiniteProducts.IdentityEnvironment

nf : ∀ {Γ σ}(t : Tm Γ σ){n : Nf Γ σ} →
     nf t ⇓ n → Σ (Nf Γ σ) λ n' → n ≡ n'
nf t (norm⇓ p p') with eval t vid p 
... | v , refl = quot v p'

