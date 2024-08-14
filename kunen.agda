{-# OPTIONS --prop --rewriting #-}

module kunen where
open import Agda.Builtin.Equality
open import Agda.Primitive
open import not-mine.logic
open import not-mine.ZF
open import not-mine.funrel
open _∧_

-- Because we are trying to work in FOL, I add the classical property of existential import.
postulate
    existential-import :
        (A : Set) → (P : A → Prop) → ((x : A) → P x) → ∃[ x ∈ A ] P x

-- "Axiom" 0. Set Existence.
-- As you can see above, this actually follows from FOL directly.
set-existence : ∃[ x ∈ 𝕍 ] (x ≗ x)
set-existence = existential-import 𝕍 (λ x → x ≗ x) (λ x → refl𝕍)

-- Definition I.6.1
emp : 𝕍 → Prop
emp x = ∀ y → ¬ y ∈ x

-- Theorem I.6.2
empty-unique : ∀ x y → emp x ∧ emp y → x ≗ y
empty-unique x y [ emp-x , emp-y ] =
    ≡-≗ (Extensional λ z → equiv-equal
        [ (λ z∈x → ex-falso (emp-x z z∈x)) ,
          (λ z∈y → ex-falso (emp-y z z∈y)) ])

private
    -- A private block, because the following axiom is inconsistent.
    -- Well, until I figure out how to actually limit postulates, let's pretend that the private block does.
    
    -- Garbage I.6.4
    -- Navie Comprehension Axiom.
    postulate
        Naive-Comprehension : (P : 𝕍 → Prop) → 𝕍
        Naive-Membership : ∀ z P → z ∈ Naive-Comprehension P ≡ P z

    {-# REWRITE Naive-Membership #-}
    syntax Naive-Comprehension (λ x → P) = ⟦ x ∥ P ⟧
    
    -- Paradox I.6.5
    russell-set : 𝕍
    russell-set = ⟦ x ∥ ¬ x ∈ x ⟧

    -- Bonus: this derivation does not use LEM, as (P ↔ ¬P) → ⊥ is derivable intuitionistically.
    intuitive : {P : Prop} → (P → ¬ P) ∧ (¬ P → P) → ⊥
    intuitive [ zig , zag ] = (λ x → zig x x) (zag (λ x → zig x x))
    
    russell-paradox : ⊥
    russell-paradox = intuitive [ zig , zag ]
        where
            zig : russell-set ∈ russell-set → ¬ russell-set ∈ russell-set
            zig yes = yes
            zag : ¬ russell-set ∈ russell-set → russell-set ∈ russell-set
            zag no = no

-- Theorem I.6.6
-- There is no set which contains all sets.
russell : 𝕍 → 𝕍
russell z = ⟦ x ∈ z ∥ ¬ x ∈ x ⟧

no-𝕍-set : ∀ x → ∃[ y ∈ 𝕍 ] ¬ y ∈ x
no-𝕍-set x = exists (russell x) λ y∈x → intuitive [ zig y∈x , zag y∈x ]
    where
        zig : russell x ∈ x → russell x ∈ russell x → ¬ russell x ∈ russell x
        zig _ [ y∈x , rx∉rx ] = rx∉rx 
        zag : russell x ∈ x → ¬ russell x ∈ russell x → russell x ∈ russell x
        zag y∈x rx∉rx = [ y∈x , rx∉rx ]

-- We skip some stuff about unions and ordered/unordered pairs, because that has been done already.

-- Relations

-- Special ∈-properties to define ordinals.
-- It gets special treatment, because this is not a set relation,
-- it is a relation on the proper class 𝕍
∈-transitive : 𝕍 → Prop
∈-transitive A = ∀ {x y z} → x ∈ A → y ∈ A → z ∈ A →
    x ∈ y → y ∈ z → x ∈ z

∈-irreflexive : 𝕍 → Prop
∈-irreflexive A = ∀ {x} → x ∈ A → ¬ x ∈ x

∈-trichotomy : 𝕍 → Prop
∈-trichotomy A = ∀ {x y} → x ∈ A → y ∈ A →
    x ∈ y ∨ y ∈ x ∨ x ≗ y
    
∈-total : 𝕍 → Prop
∈-total A = ∈-transitive A ∧ ∈-irreflexive A ∧ ∈-trichotomy A

_∈-minimal-in_ : 𝕍 → 𝕍 → Prop
_∈-minimal-in_ y X = (y ∈ X ∧ ∀ z → z ∈ X → ¬ z ∈ y)

∈-well-founded : 𝕍 → Prop
∈-well-founded A = ∀ X → ¬ X ≗ ∅ → X ⊆ A → ∃[ y ∈ 𝕍 ] (y ∈-minimal-in X)

∈-well-ordered : 𝕍 → Prop
∈-well-ordered A = ∈-total A ∧ ∈-well-founded A

transitive-set : 𝕍 → Prop
transitive-set z = ∀ y → y ∈ z → y ⊆ z

ordinal : 𝕍 → Prop
ordinal z = transitive-set z ∧ ∈-well-ordered z

-- Constructors for properties of ordinals
ordinal-is-transitive : ∀ {α} → ordinal α → ∈-transitive α
ordinal-is-transitive ord-α = π₁ (π₁ (π₁ (π₂ ord-α)))

ordinal-is-irreflexive : ∀ {α} → ordinal α → ∈-irreflexive α
ordinal-is-irreflexive ord-α = π₂ (π₁ (π₁ (π₂ ord-α)))

ordinal-has-trichotomy : ∀ {α} → ordinal α → ∈-trichotomy α
ordinal-has-trichotomy ord-α = π₂ (π₁ (π₂ ord-α))

ordinal-is-total : ∀ {α} → ordinal α → ∈-total α
ordinal-is-total ord-α = π₁ (π₂ ord-α)

ordinal-is-well-founded : ∀ {α} → ordinal α → ∈-well-founded α
ordinal-is-well-founded ord-α = π₂ (π₂ ord-α)

ordinal-is-well-ordered : ∀ {α} → ordinal α → ∈-well-ordered α
ordinal-is-well-ordered ord-α = π₂ ord-α

ordinal-is-transitive-set : ∀ {α} → ordinal α → transitive-set α
ordinal-is-transitive-set ord-α = π₁ ord-α

-- Really simple, but thus far unproved.
A∩B⊆A : ∀ {A B} → (A ∩ B) ⊆ A
A∩B⊆A = π₁  -- [ z∈A , z∈B ] = z∈A

A∩B⊆B : ∀ {A B} → (A ∩ B) ⊆ B
A∩B⊆B = π₂  -- [ z∈A , z∈B ] = z∈B

⊆-transitive : ∀ {A B C} → A ⊆ B → B ⊆ C → A ⊆ C
⊆-transitive A⊆B B⊆C z∈A = B⊆C (A⊆B z∈A)

-- Exercise I.7.21 (for ∈)
well-order-⊆-transport : ∀ {A X} → ∈-well-ordered A → X ⊆ A → ∈-well-ordered X
well-order-⊆-transport {A} {X} wo-A X⊆A = [ total-X , well-founded-X ]
    where
        total-X : ∈-total X
        total-X = [ [ trans-X , irreflexive-X ] , trichotomy-X ]
            where
                trans-X : ∈-transitive X
                trans-X x∈X y∈X z∈X x∈y y∈z =
                   (π₁ (π₁ (π₁ wo-A))) (X⊆A x∈X) (X⊆A y∈X) (X⊆A z∈X) x∈y y∈z
                irreflexive-X :  ∈-irreflexive X
                irreflexive-X x∈X = (π₂ (π₁ (π₁ wo-A))) (X⊆A x∈X)
                trichotomy-X : ∈-trichotomy X
                trichotomy-X x∈X y∈X =
                   (π₂ (π₁ wo-A)) (X⊆A x∈X) (X⊆A y∈X)
                
        well-founded-X : ∈-well-founded X
        well-founded-X Y not-∅ Y⊆X =
            (π₂ wo-A) Y not-∅ (⊆-transitive {Y} {X} {A} Y⊆X X⊆A)
        
-- Theorem I.8.5
-- The well-ordering of ON.

-- Lemma I.8.6
ON-transitive-class : ∀ {α} → ordinal α → ∀ {z} → z ∈ α → ordinal z
ON-transitive-class {α} ord-α {z} z∈α =
    [ trans-set-z , well-ordered-z ]
    where
        z⊆α : z ⊆ α
        z⊆α = (ordinal-is-transitive-set {α} ord-α) z z∈α
        trans-set-z : transitive-set z
        trans-set-z y y∈z x∈y =
            (ordinal-is-transitive {α} ord-α) (y⊆α x∈y) (z⊆α y∈z) z∈α x∈y y∈z
                where
                    y⊆α : y ⊆ α
                    y⊆α = (ordinal-is-transitive-set {α} ord-α) y (z⊆α y∈z)
        
        well-ordered-z : ∈-well-ordered z
        well-ordered-z =
            well-order-⊆-transport {α} {z} (ordinal-is-well-ordered {α} ord-α) ((ordinal-is-transitive-set {α} ord-α) z z∈α)

∩-preserves-transitive-set : ∀ {x y} → transitive-set x → transitive-set y → transitive-set (x ∩ y)
∩-preserves-transitive-set {x} {y} trans-x trans-y =
    λ z → λ { [ z∈x , z∈y ] → λ w∈z → [ (trans-x z z∈x) w∈z , (trans-y z z∈y) w∈z ] } 

-- Lemma I.8.7
∩-preserves-ordinal : ∀ {α β} → ordinal α → ordinal β → ordinal (α ∩ β)
∩-preserves-ordinal {α} {β} ord-α ord-β =
    [ ∩-preserves-transitive-set {α} {β} (ordinal-is-transitive-set {α} ord-α) (ordinal-is-transitive-set {β} ord-β) ,
      well-order-⊆-transport {α} {α ∩ β} (ordinal-is-well-ordered {α} ord-α) (A∩B⊆A {α} {β}) ]

_∖_ : 𝕍 → 𝕍 → 𝕍
_∖_ A B = ⟦ x ∈ A ∥ ¬ x ∈ B ⟧

∅-implies-empty : ∀ {A} → A ≗ ∅ → ∀ z → ¬ z ∈ A
∅-implies-empty refl𝕍 z = equal-equiv (∅-empty {z})

⊆-antisymmetry : ∀ {A B} → A ⊆ B → B ⊆ A → A ≗ B
⊆-antisymmetry A⊆B B⊆A = ≡-≗ (Extensional (λ z → equiv-equal [ A⊆B , B⊆A ]))

-- Some lemmas about setminus.
∖-not-∅ : ∀ {A B} → ¬ A ≗ B → A ⊆ B → ¬ (B ∖ A) ≗ ∅
∖-not-∅ {A} {B} ¬A≗B A⊆B eq = ¬A≗B (⊆-antisymmetry A⊆B B⊆A)
    where
        aux : ∀ {P Q} → ¬ (P ∧ ¬ Q) → (P → Q)
        aux {P} {Q} hyp p with truth Q
        ... | inj₁ yes = ≡-true yes
        ... | inj₂ no = ex-falso (hyp [ p , ≡-false no ])
        
        B⊆A : B ⊆ A
        B⊆A {z} z∈B = (aux (∅-implies-empty eq z)) z∈B
        
∖-⊆ : ∀ {A B} → (A ∖ B) ⊆ A
∖-⊆ [ x∈A , x∉B ] = x∈A

¬≗-¬≡ : ∀ {x y} → ¬ x ≗ y → (x ≡ y → ⊥)
¬≗-¬≡ ¬x≗y x≡y = ¬x≗y (≡-≗ x≡y)

-- Lemma I.8.8
⊆-is-≤ : ∀ {α β} → ordinal α → ordinal β → α ⊆ β ≡ α ∈ β ∨ α ≗ β
⊆-is-≤ {α} {β} ord-α ord-β =
    equiv-equal [ zig , zag ]
    where
        zig : α ⊆ β → α ∈ β ∨ (α ≗ β)
        zig α⊆β with truth (α ≗ β)
        ... | inj₁ eq = ι₂ (≡-true eq)
        ... | inj₂ neq = ι₁ (sublemma exists-ξ)
            where
                X : 𝕍
                X = β ∖ α
                
                exists-ξ : ∃[ y ∈ 𝕍 ] (y ∈-minimal-in X)
                exists-ξ =
                    (ordinal-is-well-founded {β} ord-β) X (∖-not-∅ (≡-false neq) α⊆β) (∖-⊆ {β} {α})
                
                sublemma : ∃[ y ∈ 𝕍 ] (y ∈-minimal-in X) → α ∈ β
                sublemma (exists ξ ξ-min-X) = equal-equiv (cong (λ x → x ∈ β) (≗-≡ (symmP α≗ξ))) ξ∈β
                    where
                        ξ∈β : ξ ∈ β
                        ξ∈β = π₁ (π₁ ξ-min-X)
                        
                        ξ⊆α : ξ ⊆ α
                        ξ⊆α {μ} μ∈ξ = μ∈α
                            where
                                μ∈β : μ ∈ β
                                μ∈β = ((ordinal-is-transitive-set {β} ord-β) ξ ξ∈β) μ∈ξ
                            
                                μ∉X : ¬ μ ∈ X
                                μ∉X μ∈X = ((π₂ ξ-min-X) μ μ∈X) μ∈ξ
                        
                                -- temporary, repetitive, ugly    
                                aux : ∀ {P Q} → ¬ (P ∧ ¬ Q) → (P → Q)
                                aux {P} {Q} hyp p with truth Q
                                ... | inj₁ yes = ≡-true yes
                                ... | inj₂ no = ex-falso (hyp [ p , ≡-false no ])
                                
                                μ∈α : μ ∈ α
                                μ∈α = (aux μ∉X) μ∈β
                        
                        α≗ξ : α ≗ ξ
                        α≗ξ with truth (ξ ≗ α)
                        ... | inj₁ eq = symmP (≡-true eq)
                        ... | inj₂ neq = another-sublemma exists-μ
                            where
                                Y : 𝕍
                                Y = α ∖ ξ
                                
                                Y-not-empty : ¬ Y ≗ ∅
                                Y-not-empty = ∖-not-∅ (≡-false neq) ξ⊆α
                                
                                exists-μ : ∃[ μ ∈ 𝕍 ] μ ∈ Y
                                exists-μ = non-empty (¬≗-¬≡ Y-not-empty)
                                    
                                another-sublemma : ∃[ μ ∈ 𝕍 ] μ ∈ Y → α ≗ ξ
                                another-sublemma (exists μ μ∈Y) = ex-falso (absurd dilemma)
                                    where
                                        ¬P→P∨Q∨R→Q∨R : {P Q R : Prop} → ¬ P → P ∨ Q ∨ R → Q ∨ R
                                        ¬P→P∨Q∨R→Q∨R {P} {Q} {R} ¬p (ι₁ (ι₁ p)) = ex-falso (¬p p)
                                        ¬P→P∨Q∨R→Q∨R {P} {Q} {R} ¬p (ι₁ (ι₂ q)) = ι₁ q
                                        ¬P→P∨Q∨R→Q∨R {P} {Q} {R} ¬p (ι₂ r) = ι₂ r
                                        -- solve 1 (λ P Q R → (¡ P ==> P ||| Q ||| R ==> Q ||| R)) P Q R
                                        -- Solver can't handle multiple proposition variables?
                                    
                                        μ∈β : μ ∈ β
                                        μ∈β = α⊆β (π₁ μ∈Y)
                                    
                                        dilemma : ξ ∈ μ ∨ μ ≗ ξ
                                        dilemma = ¬P→P∨Q∨R→Q∨R (π₂ μ∈Y) ((ordinal-has-trichotomy {β} ord-β) μ∈β ξ∈β)
                                        
                                        absurd : ξ ∈ μ ∨ μ ≗ ξ → ⊥
                                        absurd (ι₁ ξ∈μ) =
                                            (π₂ (π₁ ξ-min-X)) (((ordinal-is-transitive-set {α} ord-α) μ (π₁ μ∈Y)) ξ∈μ)
                                        absurd (ι₂ refl𝕍) = (π₂ (π₁ ξ-min-X)) (π₁ μ∈Y)
        
        zag : α ∈ β ∨ (α ≗ β) → α ⊆ β
        zag (ι₁ α∈β) = (ordinal-is-transitive-set {β} ord-β) α α∈β
        zag (ι₂ refl𝕍) = idP

≗-trans : ∀ {a b c} → a ≗ b → b ≗ c → a ≗ c
≗-trans refl𝕍 refl𝕍 = refl𝕍

≗-transport : ∀ {a b} (f : 𝕍 → Prop) → a ≗ b → f a → f b
≗-transport f refl𝕍 fa = fa

-- Proof of Theorem I.8.5
-- (1)
∈-transitive-on-ON :
    ∀ {α β γ} → ordinal α → ordinal β → ordinal γ → α ∈ β → β ∈ γ → α ∈ γ
∈-transitive-on-ON {α} {β} {γ} ord-α ord-β ord-γ α∈β β∈γ =
    (((ordinal-is-transitive-set {γ} ord-γ) β) β∈γ) α∈β
    
-- (2)
∈-irrefelxive-on-ON : ∀ {α} → ordinal α → ¬ α ∈ α
∈-irrefelxive-on-ON {α} ord-α α∈α = ((ordinal-is-irreflexive {α} ord-α) α∈α) α∈α

-- (3)
∈-has-trichotomy-on-ON : ∀ {α β} → ordinal α → ordinal β → α ∈ β ∨ β ∈ α ∨ α ≗ β
∈-has-trichotomy-on-ON {α} {β} ord-α ord-β =
    sublemma (equal-equiv (⊆-is-≤ ord-δ ord-α) δ⊆α) (equal-equiv (⊆-is-≤ ord-δ ord-β) δ⊆β)
    where
        δ : 𝕍
        δ = α ∩ β

        ord-δ : ordinal δ
        ord-δ = ∩-preserves-ordinal {α} {β} ord-α ord-β
        
        δ⊆α : δ ⊆ α
        δ⊆α = A∩B⊆A {α} {β}
        
        δ⊆β : δ ⊆ β
        δ⊆β = A∩B⊆B {α} {β}
        
        sublemma : δ ∈ α ∨ δ ≗ α → δ ∈ β ∨ δ ≗ β → α ∈ β ∨ β ∈ α ∨ α ≗ β
        sublemma (ι₁ δ∈α) (ι₁ δ∈β) = ex-falso (∈-irrefelxive-on-ON {δ} ord-δ δ∈δ)
            where
                δ∈δ : δ ∈ δ
                δ∈δ = [ δ∈α , δ∈β ]
        sublemma (ι₂ δ≗α) (ι₁ δ∈β) = ι₁ (ι₁ ((≗-transport (λ x → x ∈ β) δ≗α) δ∈β))
        sublemma (ι₁ δ∈α) (ι₂ δ≗β) = ι₁ (ι₂ ((≗-transport (λ x → x ∈ α) δ≗β) δ∈α)) 
        sublemma (ι₂ δ≗α) (ι₂ δ≗β) = ι₂ (≗-trans (symmP δ≗α) δ≗β)
        
-- (4)
∈-well-founded-on-ON : ∀ {X} → ¬ X ≗ ∅ → (∀ z → z ∈ X → ordinal z) → ∃[ y ∈ 𝕍 ] (y ∈-minimal-in X)
∈-well-founded-on-ON {X} ¬X≗∅ X⊆ON = sublemma exists-α
    where
        exists-α : ∃[ α ∈ 𝕍 ] α ∈ X
        exists-α = non-empty (¬≗-¬≡ ¬X≗∅)
        
        sublemma : ∃[ α ∈ 𝕍 ] α ∈ X → ∃[ y ∈ 𝕍 ] (y ∈-minimal-in X)
        sublemma (exists α α∈X) with truth (α ∈-minimal-in X)
        ... | inj₁ yes = exists α (≡-true yes)
        ... | inj₂ no = exists-ξ-least
            where
                Y : 𝕍
                Y = α ∩ X
                
                α∩X-nonempty : ¬ (α ∩ X) ≗ ∅
                α∩X-nonempty = ∃-to-¬∅ α∩β-nonempty-∃
                    where
                        DeMorgan-∧∨ : {P Q : Prop} → ¬ (P ∧ Q) → ¬ P ∨ ¬ Q
                        DeMorgan-∧∨ {P} {Q} ¬[P∧Q] with truth P | truth Q
                        ... | inj₁ p | inj₁ q = ex-falso (¬[P∧Q] [ ≡-true p , ≡-true q ] )
                        ... | _ | inj₂ ¬q = ι₂ (≡-false ¬q)
                        ... | inj₂ ¬p | _ = ι₁ (≡-false ¬p)
                        
                        ¬[P→¬Q]→P∧Q : {P Q : Prop} → ¬(P → ¬ Q) → P ∧ Q
                        ¬[P→¬Q]→P∧Q {P} {Q} ¬[p→¬q] with truth P | truth Q
                        ... | inj₁ p | inj₁ q = [ ≡-true p , ≡-true q ]
                        ... | _ | inj₂ ¬q = ex-falso (¬[p→¬q] (λ p → (≡-false ¬q)))
                        ... | inj₂ ¬p | _ = ex-falso (¬[p→¬q] (λ p → ex-falso ((≡-false ¬p) p)))
                        
                        P→¬P∨Q→Q : {P Q : Prop} → P → ¬ P ∨ Q → Q
                        P→¬P∨Q→Q p (ι₁ ¬p) = ex-falso (¬p p)
                        P→¬P∨Q→Q p (ι₂ q) = q
                        
                        ¬∃-∀¬ : {P : 𝕍 → Prop} → ¬ (∃[ x ∈ 𝕍 ] P x) → (∀ x → ¬ P x)
                        ¬∃-∀¬ ¬∃ x Px = ¬∃ (exists x Px)
                        
                        ¬¬P→P : {P : Prop} → ¬ ¬ P → P
                        ¬¬P→P {P} = solve 1 (\ P -> (¡ ¡ P ==> P)) P
                        
                        ¬∀-∃¬ : {P : 𝕍 → Prop} → ¬ (∀ x → P x) → ∃[ x ∈ 𝕍 ] ¬ P x
                        ¬∀-∃¬ {P} ¬∀ with truth (∃[ x ∈ 𝕍 ] ¬ P x)
                        ... | inj₁ yes = ≡-true yes
                        ... | inj₂ no = ex-falso (¬∀ (λ x → ¬¬P→P (¬∃-∀¬ (≡-false no) x)))
                        
                        lol : ∀ {A B} → A ⊆ B → ∃[ y ∈ 𝕍 ] y ∈ A → ∃[ y ∈ 𝕍 ] y ∈ (A ∩ B)
                        lol A⊆B (exists y y∈A) = exists y ([ y∈A , A⊆B y∈A ])
                        
                        ∃-to-¬∅ : ∀ {A} → ∃[ y ∈ 𝕍 ] y ∈ A → ¬ A ≗ ∅
                        ∃-to-¬∅ (exists absurd absurd∈∅) refl𝕍 = absurd∈∅
                        
                        ∃-prop-transfer : {P Q : Prop} → (P → Q) → ∃[ y ∈ 𝕍 ] P → ∃[ y ∈ 𝕍 ] Q
                        ∃-prop-transfer p→q (exists y p) = exists y (p→q p)
                        
                        ∃-prop-transfer-param : {P Q : 𝕍 → Prop} → {x : 𝕍} → (∀ {x} → P x → Q x) → ∃[ y ∈ 𝕍 ] P x → ∃[ y ∈ 𝕍 ] Q x
                        ∃-prop-transfer-param px→qx (exists y px) = exists y (px→qx px)
                        
                        ∧-comm : {P Q : Prop} → P ∧ Q → Q ∧ P
                        ∧-comm [ p , q ] = [ q , p ]
                        
                        α∩β-nonempty-∃ : ∃[ y ∈ 𝕍 ] y ∈ Y
                        α∩β-nonempty-∃ =
                            -- ∃-prop-transfer-param (¬[P→¬Q]→P∧Q) (¬∀-∃¬ {λ y → y ∈ X → ¬ y ∈ α} (P→¬P∨Q→Q (α∈X) (DeMorgan-∧∨ (≡-false no))))
                            subsublemma (¬∀-∃¬ {λ z → z ∈ X → ¬ z ∈ α} (P→¬P∨Q→Q (α∈X) (DeMorgan-∧∨ (≡-false no))))
                            where
                                subsublemma : ∃[ x ∈ 𝕍 ] ¬ (x ∈ X → ¬ x ∈ α) → ∃[ x ∈ 𝕍 ] x ∈ α ∧ x ∈ X
                                subsublemma (exists x impl) = exists x (∧-comm (¬[P→¬Q]→P∧Q impl))
                
                exists-ξ-least : ∃[ ξ ∈ 𝕍 ] ξ ∈-minimal-in X
                exists-ξ-least = subsublemma (ordinal-is-well-founded {α} (X⊆ON α α∈X) Y α∩X-nonempty (A∩B⊆A {α} {X}))
                    where
                        subsublemma : ∃[ ξ ∈ 𝕍 ] ξ ∈-minimal-in Y → ∃[ ξ ∈ 𝕍 ] ξ ∈-minimal-in X
                        subsublemma (exists ξ [ ξ∈Y , ξ-min ]) =
                            exists ξ [ π₂ ξ∈Y , ξ-min-in-X ]
                                where
                                    ξ-min-in-X : ∀ z → z ∈ X → ¬ z ∈ ξ
                                    ξ-min-in-X z z∈X z∈ξ = (ξ-min z z∈α∩X) z∈ξ
                                        where
                                            z∈α∩X : z ∈ Y
                                            z∈α∩X = [ ((ordinal-is-transitive-set {α} (X⊆ON α α∈X)) ξ (π₁ ξ∈Y)) z∈ξ , z∈X ]

infix 8 _↔_
_↔_ : Prop → Prop → Prop
_↔_ P Q = (P → Q) ∧ (Q → P)

-- Theorem I.8.9
-- ON is a proper class.
Burali-Forti-Paradox : ∃[ ON ∈ 𝕍 ] (∀ z → z ∈ ON ↔ ordinal z) → ⊥
Burali-Forti-Paradox (exists ON all-ords) = (ordinal-is-irreflexive {ON} ON-ordinal) ON∈ON ON∈ON
    where
        z∈ON→ord-z : ∀ {z} → z ∈ ON → ordinal z
        z∈ON→ord-z {z} = π₁ (all-ords z)
        
        ord-z→z∈ON : ∀ {z} → ordinal z → z ∈ ON
        ord-z→z∈ON {z} = π₂ (all-ords z)
        
        ON-ordinal : ordinal ON
        ON-ordinal = [ trans-set-ON , [ [ [ trans-ON , irreflexive-ON ] , trichotomy-on-ON ] , well-founded-ON ] ]
            where
                trans-set-ON : transitive-set ON
                trans-set-ON y y∈ON z∈y = ord-z→z∈ON (ON-transitive-class {y} (z∈ON→ord-z y∈ON) z∈y)
                
                irreflexive-ON : ∈-irreflexive ON
                irreflexive-ON {x} x∈ON = ∈-irrefelxive-on-ON {x} (z∈ON→ord-z x∈ON)
                
                trans-ON : ∈-transitive ON
                trans-ON {x} {y} {z} x∈ON y∈ON z∈ON =
                    ∈-transitive-on-ON {x} {y} {z} (z∈ON→ord-z x∈ON) (z∈ON→ord-z y∈ON) (z∈ON→ord-z z∈ON)
                
                trichotomy-on-ON : ∈-trichotomy ON
                trichotomy-on-ON {x} {y} x∈ON y∈ON =
                    ∈-has-trichotomy-on-ON {x} {y} (z∈ON→ord-z x∈ON) (z∈ON→ord-z y∈ON)
                
                well-founded-ON : ∈-well-founded ON
                well-founded-ON X X-nonempty X⊆ON =
                    ∈-well-founded-on-ON {X} X-nonempty X-full-of-ords
                        where
                            X-full-of-ords : ∀ z → z ∈ X → ordinal z
                            X-full-of-ords z z∈X = z∈ON→ord-z (X⊆ON z∈X)
                
        ON∈ON : ON ∈ ON
        ON∈ON = ord-z→z∈ON  ON-ordinal
        