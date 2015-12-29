module BasicSystem.Syntax where

infix 10 _≡ˠ_
infix 10 _≡⁺_
infix 10 _≡ˢ_
infix 10 _≡_
infixl 50 _•_

mutual 
  data Con : Set where
    ε   : Con
    _,_ : ∀ Γ → Ty Γ → Con

  data _≡ˠ_ : Con → Con → Set where
    congε : ε ≡ˠ ε
    cong, : ∀ {Γ Γ' σ σ'} → Γ ≡ˠ Γ' → σ ≡⁺ σ' → (Γ , σ) ≡ˠ (Γ' , σ')

  data Ty : Con → Set where
    coe⁺  : ∀ {Γ Δ} → Ty Γ → Γ ≡ˠ Δ → Ty Δ
    _[_]⁺ : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    U     : ∀ {Γ} → Ty Γ
    El    : ∀ {Γ} → Tm Γ U → Ty Γ
    Π     : ∀ {Γ} σ → Ty (Γ , σ) → Ty Γ

  _,'_ : ∀ Γ → Ty Γ → Con
  _,'_ = _,_
  Π' : ∀ {Γ} σ → Ty (Γ ,' σ) → Ty Γ
  Π' = Π
  U' : ∀ {Γ} → Ty Γ
  U' = U

  data Sub : Con → Con → Set where
    coeˢ : ∀ {Γ Γ' Δ Δ'} → Sub Γ Δ → Γ ≡ˠ Γ' → Δ ≡ˠ Δ' → 
           Sub Γ' Δ'
    _•_  : ∀ {B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
    id   : ∀ {Γ} → Sub Γ Γ
    pop  : ∀ {Γ} σ → Sub (Γ , σ) Γ
    _<_ : ∀ {Γ Δ σ}(ts : Sub Γ Δ) → Tm Γ (σ [ ts ]⁺) → 
          Sub Γ (Δ , σ)

  _⇒_ : ∀ {Γ} → Ty Γ → Ty Γ → Ty Γ
  σ ⇒ τ = Π σ (τ [ pop σ ]⁺)

  _•'_ : ∀ {B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
  _•'_ = _•_
  id' : ∀ {Γ} → Sub Γ Γ
  id' = id
  _[_]⁺' : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
  _[_]⁺' = _[_]⁺
  pop'  : ∀ {Γ} σ → Sub (Γ ,' σ) Γ
  pop' = pop

  data _≡⁺_ : ∀ {Γ Γ'} → Ty Γ → Ty Γ' → Set where
    -- Setoid boilerplate
    coh⁺  : ∀ {Γ}{Δ}(σ : Ty Γ)(p : Γ ≡ˠ Δ) → coe⁺ σ p ≡⁺ σ

    -- Equivalence boilerplate
    refl⁺ : ∀ {Γ}{σ : Ty Γ} → σ ≡⁺ σ
    trans⁺ : ∀ {Γ}{Γ'}{Γ''}{σ : Ty Γ}{σ' : Ty Γ'}{σ'' : Ty Γ''} → 
             σ ≡⁺ σ' → σ' ≡⁺ σ'' → σ ≡⁺ σ''
    sym⁺  : ∀ {Γ}{Γ'}{σ : Ty Γ}{σ' : Ty Γ'} → σ ≡⁺ σ' → σ' ≡⁺ σ
    
    -- Substitution boilerplate
    rightid⁺ : ∀ {Γ}{σ : Ty Γ} → σ [ id' ]⁺ ≡⁺ σ
    assoc⁺ : ∀ {B}{Γ}{Δ}{σ}{ts : Sub Γ Δ}{us : Sub B Γ} → 
            σ [ ts ]⁺ [ us ]⁺  ≡⁺ σ [ ts • us ]⁺
    cong⁺ : ∀ {Γ Γ'}{Δ Δ'}{σ}{σ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'} → 
           σ ≡⁺ σ' → ts ≡ˢ ts' →
           σ [ ts ]⁺ ≡⁺ σ' [ ts' ]⁺

    -- Congruence boilerplate
    congU : ∀ {Γ}{Γ'} → Γ ≡ˠ Γ' → U {Γ} ≡⁺ U {Γ'}
    congEl : ∀ {Γ Γ'}{t : Tm Γ U}{t' : Tm Γ' U} → Γ ≡ˠ Γ' → t ≡ t' → 
             El t ≡⁺ El t'
    congΠ : ∀ {Γ}{σ : Ty Γ}{τ : Ty (Γ , σ)} → 
         ∀ {Γ'}{σ' : Ty Γ'}{τ' : Ty (Γ' , σ')} → 
         (p : σ ≡⁺ σ')(q : τ ≡⁺ τ') →
         Π σ τ ≡⁺ Π σ' τ'

    -- Computation rules
    U[] : ∀ {Γ}{Δ}{ts : Sub Γ Δ} → U [ ts ]⁺ ≡⁺ U {Γ}
    El[] : ∀ {Γ}{Δ}{t : Tm Δ U}{ts : Sub Γ Δ} → 
           El t [ ts ]⁺ ≡⁺ Elˢ (t [ ts ]')
    Π[] : ∀ {Γ}{Δ}{σ}{τ}{ts : Sub Γ Δ} → 
          Π σ τ [ ts ]⁺ ≡⁺ Π (σ [ ts ]⁺) (τ [ ts ↗  σ ]⁺)

    -- equality projections
    dom : ∀ {Γ Γ' σ σ'}{τ : Ty (Γ , σ)}{τ' : Ty (Γ' , σ')} →
          Π σ τ ≡⁺ Π σ' τ' → σ ≡⁺ σ'
    cod : ∀ {Γ Γ' σ σ'}{τ : Ty (Γ , σ)}{τ' : Ty (Γ' , σ')} → Π σ τ ≡⁺ Π σ' τ' → τ ≡⁺ τ'

  data _≡ˢ_ : ∀ {Γ Γ' Δ Δ'} → Sub Γ Δ → Sub Γ' Δ' → Set where
    -- Setoid boilerplate
    cohˢ : ∀ {Γ Γ' Δ Δ'}(ts : Sub Γ Δ)(p : Γ ≡ˠ Γ')(q : Δ ≡ˠ Δ') →
            coeˢ ts p q  ≡ˢ ts

    -- Equivalence boilerplate
    reflˢ : ∀ {Γ}{Δ}{ts : Sub Γ Δ} → ts ≡ˢ ts
    transˢ : ∀ {Γ Γ' Γ''}{Δ Δ' Δ''} → 
             {ts : Sub Γ Δ}{ts' : Sub Γ' Δ'}{ts'' : Sub Γ'' Δ''} → 
             ts ≡ˢ ts' → ts' ≡ˢ ts'' → ts ≡ˢ ts''
    symˢ : ∀ {Γ Γ'}{Δ Δ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'} →
           ts ≡ˢ ts' → ts' ≡ˢ ts

    -- Subsitution boilerplate
    rightidˢ : ∀ {Γ}{Δ}{ts : Sub Γ Δ} → (ts • id) ≡ˢ ts
    assocˢ : ∀ {A}{B}{Γ}{Δ}{ts : Sub Γ Δ}{us : Sub B Γ}{vs : Sub A B} →
         (ts • us • vs) ≡ˢ ts • (us • vs)

    -- Congruence boilerplate
    cong• : ∀ {B B' Γ Γ' Δ Δ'}{ts : Sub Γ Δ}{us : Sub B Γ} →
            {ts' : Sub Γ' Δ'}{us' : Sub B' Γ'} → ts ≡ˢ ts' → us ≡ˢ us' →
            ts • us ≡ˢ ts' • us'
    congid : ∀ {Γ Γ'} → Γ ≡ˠ Γ' → id {Γ} ≡ˢ id {Γ'}
    congpop : ∀ {Γ Γ'}{σ : Ty Γ}{σ' : Ty Γ'} → 
         σ ≡⁺ σ' →  pop σ ≡ˢ pop σ'
    cong< : ∀ {Γ Γ'}{Δ Δ'}{σ}{σ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'}
          {t : Tm Γ (σ [ ts ]⁺)}{t' : Tm Γ' (σ' [ ts' ]⁺)} → 
          ts ≡ˢ ts' → t ≡ t' → (ts < t) ≡ˢ (ts' < t')

    -- Computation rules
    leftid : ∀ {Γ}{Δ}{ts : Sub Γ Δ} → (id • ts) ≡ˢ ts
    pop< : ∀ {Γ}{Δ}{σ}{ts : Sub Γ Δ}{t : Tm Γ (σ [ ts ]⁺)} → 
           (pop σ • (ts < t)) ≡ˢ ts
    •< : ∀ {B}{Γ}{Δ}{σ} → 
         {ts : Sub Γ Δ}{t : Tm Γ (σ [ ts ]⁺)}{us : Sub B Γ} → 
         (ts < t) • us ≡ˢ (ts • us < coe' (t [ us ]') assoc⁺)
    poptop : ∀ {Γ}{σ} → (pop σ < top') ≡ˢ id {Γ , σ}

  data Tm : ∀ Γ → Ty Γ → Set where
    coe  : ∀ {Γ Γ' σ σ'} → Tm Γ σ → σ ≡⁺ σ' → Tm Γ' σ'
    _[_] : ∀ {Γ Δ σ} → Tm Δ σ → (ts : Sub Γ Δ) → Tm Γ (σ [ ts ]⁺)
    top  : ∀ {Γ σ} → Tm (Γ , σ) (σ [ pop σ ]⁺)
    λt   : ∀ {Γ σ τ} → Tm (Γ , σ) τ → Tm Γ (Π σ τ)
    app  : ∀ {Γ σ τ} → Tm Γ (Π σ τ) → Tm (Γ , σ) τ

  El' : ∀ {Γ} → Tm Γ U' → Ty Γ
  El' = El
  _[_]' : ∀ {Γ Δ σ} → Tm Δ σ → (ts : Sub Γ Δ) → Tm Γ (σ [ ts ]⁺')
  _[_]' = _[_]
  _<'_ : ∀ {Γ Δ σ}(ts : Sub Γ Δ) → Tm Γ (σ [ ts ]⁺') → 
        Sub Γ (Δ ,' σ)
  _<'_ = _<_
  top' : ∀ {Γ σ} → Tm (Γ ,' σ) (σ [ pop' σ ]⁺')
  top' = top  
  coe' : ∀ {Γ Γ' σ σ'} → Tm Γ σ → σ ≡⁺ σ' → Tm Γ' σ'
  coe' = coe

  -- smart constructors
  sub⁺ : ∀ {Γ σ} → Ty (Γ ,' σ) → Tm Γ σ → Ty Γ
  sub⁺ σ t = σ [ id < t [ id ]' ]⁺ 

  Elˢ : ∀ {Γ Δ}{ts : Sub Γ Δ} → Tm Γ (U' [ ts ]⁺') → Ty Γ
  Elˢ σ = El (coe σ U[])  

  Els : ∀ {Γ σ}{t : Tm Γ σ} → Tm Γ (sub⁺ U' t) → Ty Γ
  Els σ = El (coe σ U[]) 

  sub : ∀ {Γ σ τ} → Tm (Γ ,' σ) τ → (a : Tm Γ σ) → Tm Γ (sub⁺ τ a)
  sub u t = u [ id < t [ id ] ] 

  _$_ : ∀ {Γ σ τ} → Tm Γ (Π' σ τ) → (a : Tm Γ σ) → Tm Γ (sub⁺ τ a)
  f $ a = sub (app f) a  

  _↗_ : ∀ {Γ Δ}(ts : Sub Γ Δ)(σ : Ty Δ) → Sub (Γ ,' σ [ ts ]⁺') (Δ ,' σ)
  ts ↗ σ = ts • pop _ < coe top assoc⁺ 

  _↑_ : ∀ {Γ Δ}(ts : Sub Γ Δ)(σ : Tm Δ U') → 
        Sub (Γ ,' Elˢ (σ [ ts ]')) (Δ ,' El' σ)
  ts ↑ σ = ts • pop _ < coe top (trans⁺ (cong⁺ (sym⁺ El[]) reflˢ) assoc⁺)

  data _≡_ : ∀ {Γ Γ' σ σ'} → Tm Γ σ → Tm Γ' σ' → Set where
    -- Setoid boilerplate
    coh  : ∀ {Γ}{Γ'}{σ : Ty Γ}{σ' : Ty Γ'}(t : Tm Γ σ)(p : σ ≡⁺ σ') →
           coe t p ≡ t

    -- Equivalence boilerplate
    refl : ∀ {Γ}{σ}{t : Tm Γ σ} → t ≡ t
    sym : ∀ {Γ}{Γ'}{σ}{σ'}{t : Tm Γ σ}{t' : Tm Γ' σ'} → 
          t ≡ t' → t' ≡ t
    trans : ∀ {Γ Γ' Γ''}{σ}{σ'}{σ''} →
           {t : Tm Γ σ}{t' : Tm Γ' σ'}{t'' : Tm Γ'' σ''} → 
           t ≡ t' → t' ≡ t'' → t ≡ t''

    -- Substitution boilerplate
    rightid : ∀ {Γ}{σ : Ty Γ}{t : Tm Γ σ} → t [ id ] ≡ t
    assoc : ∀ {B}{Γ}{Δ}{σ}{t : Tm Δ σ}{ts : Sub Γ Δ}{us : Sub B Γ} → 
            t [ ts ] [ us ]  ≡  t [ ts • us ]
    cong : ∀ {Γ Γ'}{Δ Δ'}{σ : Ty Δ}{σ' : Ty Δ'} →
          {t : Tm Δ σ}{t' : Tm Δ' σ'}{ts : Sub Γ Δ}{ts' : Sub Γ' Δ'} →
          t ≡ t' → ts ≡ˢ ts' →
          t [ ts ] ≡ t' [ ts' ]

    -- Congruence boilerplate
    congtop : ∀ {Γ Γ'}{σ : Ty Γ}{σ' : Ty Γ'} → σ ≡⁺ σ' → 
              top {σ = σ} ≡ top {σ = σ'}
    congλ : ∀ {Γ Γ' σ σ' τ τ'}
         {t : Tm (Γ , σ) τ}{t' : Tm (Γ' , σ') τ'} → σ ≡⁺ σ' →
         t ≡ t' → λt t ≡ λt t'
    congapp : ∀ {Γ Γ' σ σ' τ τ'} → 
         {t : Tm Γ (Π σ τ)}{t' : Tm Γ' (Π σ' τ')} → t ≡ t' → app t ≡ app t'

    -- computation rules
--    η : ∀ {Γ σ τ}{f : Tm Γ (Π σ τ)} → 
--        λ (app f) ≡ f
    β : ∀ {Γ σ τ}{t : Tm (Γ , σ) τ} →
        app (λt t) ≡ t
    top< : ∀ {Γ Δ σ}{ts : Sub Γ Δ}{t : Tm Γ (σ [ ts ]⁺)} →
           top [ ts < t ] ≡ t
    λ[] : ∀ {Γ Δ σ τ}{t : Tm (Δ , σ) τ}{ts : Sub Γ Δ} →
          coe (λt t [ ts ]) Π[] ≡ λt (t [ ts ↗ σ ])
    app[] : ∀ {Γ Δ σ τ}{f : Tm Δ (Π σ τ)}{ts : Sub Γ Δ} →
           app (coe (f [ ts ]) Π[]) ≡ app f [ ts ↗  σ ]


  reflˠ : ∀ {Γ} → Γ ≡ˠ Γ
  reflˠ {ε} = congε 
  reflˠ {Γ , σ} = cong, (reflˠ {Γ}) refl⁺

  symˠ : ∀ {Γ Γ'} → Γ ≡ˠ Γ' → Γ' ≡ˠ Γ
  symˠ congε  = congε 
  symˠ (cong, p q)  = cong, (symˠ p) (sym⁺ q) 

  transˠ : ∀ {Γ Γ' Γ''} → Γ ≡ˠ Γ' → Γ' ≡ˠ Γ'' → Γ ≡ˠ Γ''
  transˠ congε congε = congε 
  transˠ (cong, p q) (cong, p' q') = cong, (transˠ p p') (trans⁺ q q') 

  _$ˢ_ : ∀ {Γ Δ σ τ}{ts : Sub Γ Δ} → 
         Tm Γ (Π' σ τ [ ts ]⁺') →
         (a : Tm Γ (σ [ ts ]⁺')) →
         Tm Γ (τ [ ts <' a ]⁺')
  f $ˢ a = 
    coe 
      (coe f Π[] $ a) 
      (trans⁺ 
         (trans⁺ 
            assoc⁺ 
            (trans⁺ 
               (cong⁺ 
                  refl⁺ 
                  (transˢ 
                     (transˢ 
                        •< 
                        (cong< 
                           (transˢ assocˢ (cong• reflˢ pop<))
                           (trans 
                              (coh _ _) 
                              (trans 
                                 (trans (cong (coh _ _) reflˢ) top<)
                                 (sym (coh _ _))))))
                     (symˢ •<)))
               (sym⁺ assoc⁺)))
         rightid⁺)
