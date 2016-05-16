module Ch6 where

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Unit using (⊤; tt)

A : Set
A = ℕ

_<=_ : A → A → Set
a <= b = a ≤ b

tot : (a b : A) → (a <= b) ⊎ (b <= a)
tot zero b = inj₁ z≤n
tot a zero = inj₂ z≤n
tot (suc a) (suc b) with tot a b
... | inj₁ x = inj₁ (s≤s x)
... | inj₂ y = inj₂ (s≤s y)

antisym : {a b : A} → a <= b → b <= a → a ≡ b
antisym z≤n z≤n = refl
antisym (s≤s x) (s≤s y) = cong suc (antisym x y)

reflec : (a : A) → a <= a
reflec zero = z≤n
reflec (suc a) = s≤s (reflec a)

trans : {a b c : A} → a <= b → b <= c → a <= c
trans z≤n y = z≤n
trans (s≤s x) (s≤s y) = s≤s (trans x y)

data BTree : Set where
  lf : BTree
  nd : A → BTree → BTree → BTree

all-leq : BTree → A → Set
all-leq lf a = ⊤
all-leq (nd x l r) a = (x <= a) × all-leq l a × all-leq r a

all-geq : BTree → A → Set
all-geq lf a = ⊤
all-geq (nd x l r) a = (a <= x) × all-geq l a × all-geq r a

Sorted : BTree → Set
Sorted lf = ⊤
Sorted (nd a l r) = (all-geq l a × Sorted l) × (all-leq r a × Sorted r)

insert : A → BTree → BTree
insert a lf = nd a lf lf
insert a (nd b l r) with tot a b
... | inj₁ _ = nd b l (insert a r)
... | inj₂ _ = nd b (insert a l) r

-- How do you check the type of an expression, like px below for example
all-leq-ins : (t : BTree) → (a b : A) → all-leq t b → a <= b → all-leq (insert a t) b
all-leq-ins lf a b _ pa = pa , tt , tt
all-leq-ins (nd x l r) a b (px , pl , pr) pa with tot a x
... | inj₁ _ = px , pl , all-leq-ins r a b pr pa
... | inj₂ _ = px , all-leq-ins l a b pl pa , pr

-- When you have an = ? hole, what's the right way to convert it to a with ... = ?
all-geq-ins : (t : BTree) → (a b : A) → all-geq t b → b <= a → all-geq (insert a t) b
all-geq-ins lf a b x pb = pb , tt , tt
all-geq-ins (nd x l r) a b (px , pl , pr) pa with tot a x
... | inj₁ _ = px , pl , all-geq-ins r a b pr pa
... | inj₂ _ = px , all-geq-ins l a b pl pa , pr

sorted : (a : A) → (t : BTree) → Sorted t → Sorted (insert a t)
sorted a lf _ = (tt , tt) , (tt , tt)
sorted a (nd b l r) ((pl₁ , pl₂) , (pr₁ , pr₂)) with tot a b
... | inj₁ h = ((pl₁ , pl₂), (all-leq-ins r a b pr₁ h , sorted a r pr₂))
... | inj₂ h = ((all-geq-ins l a b pl₁ h , sorted a l pl₂), (pr₁ , pr₂))

insert′ : A → (t : BTree) → Sorted t → Σ[ t′ ∈  BTree ] (Sorted t′)
sorted′ : (a : A) → (t : BTree) → (s : Sorted t) → Sorted (proj₁ (insert′ a t s))
all-leq-ins′ : (t : BTree) → (s : Sorted t) → (a b : A) → all-leq t b → a <= b → all-leq (proj₁ (insert′ a t s)) b
all-geq-ins′ : (t : BTree) → (s : Sorted t) → (a b : A) → all-geq t b → b <= a → all-geq (proj₁ (insert′ a t s)) b

all-leq-ins′ lf s a b x x₁ = {!x₁ , tt , tt!} -- What's going on here C-c C-.
all-leq-ins′ (nd x t t₁) s a b x₁ x₂ = {!!}

all-geq-ins′ = {!!}

insert′ a lf _ = nd a lf lf , ((tt , tt) , (tt , tt))
insert′ a (nd b l r) ((pl₁ , pl₂) , (pr₁ , pr₂)) with tot a b
... | inj₁ h = nd b l (proj₁ (insert′ a r pr₂)) , ((pl₁ , pl₂), (all-leq-ins′ r pr₂ a b pr₁ h , sorted′ a r pr₂))
... | inj₂ h = nd b (proj₁ (insert′ a l pl₂)) r , ((all-geq-ins′ l pl₂ a b pl₁ h , sorted′ a l pl₂), (pr₁ , pr₂))

sorted′ a lf _ = (tt , tt) , (tt , tt)
sorted′ a (nd b l r) ((pl₁ , pl₂) , (pr₁ , pr₂)) with tot a b
... | inj₁ h = ((pl₁ , pl₂), (all-leq-ins′ r pr₂ a b pr₁ h , sorted′ a r pr₂))
... | inj₂ h = ((all-geq-ins′ l pl₂ a b pl₁ h , sorted′ a l pl₂), (pr₁ , pr₂))

mutual
  data BSTree : Set where
    slf : BSTree
    snd : (a : A) → (l r : BSTree) → (l >=T a) → (r <=T a) → BSTree
  
  _>=T_ : BSTree → A → Set
  slf >=T a = ⊤
  (snd x l r _ _) >=T a = (a <= x) × (r >=T a)
  
  _<=T_ : BSTree → A → Set
  slf <=T a = ⊤
  (snd x l r _ _) <=T a = (x <= a) × (l <=T a)

bst2bt : BSTree → BTree
bst2bt slf = lf
bst2bt (snd x l r _ _) = nd x (bst2bt l) (bst2bt r)

bst-sorted : (t : BSTree) → Sorted (bst2bt t)
all-leq-bst2bt : (a : A) → (t : BSTree) → (t <=T a) → all-leq (bst2bt t) a
all-geq-bst2bt : (a : A) → (t : BSTree) → (t >=T a) → all-geq (bst2bt t) a
geq-tree-trans : (t : BSTree) → (x a : A) → a <= x → t >=T x → t >=T a
leq-tree-trans : (t : BSTree) → (x a : A) → x <= a → t <=T x → t <=T a

bst-sorted slf = tt
bst-sorted (snd x l r pl pr) = ((all-geq-bst2bt x l pl , bst-sorted l) , (all-leq-bst2bt x r pr , bst-sorted r))

geq-tree-trans slf x a pa pt = tt
geq-tree-trans (snd x l r pl pr) x₁ a pa (p₁ , p₂) = trans pa p₁ , geq-tree-trans r x₁ a pa p₂

leq-tree-trans slf x a pa pt = tt
leq-tree-trans (snd x l r pl pr) x₁ a pa (p₁ , p₂) = trans p₁ pa , leq-tree-trans l x₁ a pa p₂

all-geq-bst2bt a slf x = tt
all-geq-bst2bt a (snd x l r x1 x2) (p₁ , p₂) = p₁ , all-geq-bst2bt a l (geq-tree-trans l x a p₁ x1) , all-geq-bst2bt a r p₂

all-leq-bst2bt a slf x = tt
all-leq-bst2bt a (snd x l r x1 x2) (p₁ , p₂) = p₁ , all-leq-bst2bt a l p₂ , all-leq-bst2bt a r (leq-tree-trans r x a p₁ x2)

sorted-bt2bst : (t : BTree) → Sorted t → BSTree
all-geq-bt2bst : (t : BTree) → (s : Sorted t) → (x : A) → all-geq t x → sorted-bt2bst t s >=T x
all-leq-bt2bst : (t : BTree) → (s : Sorted t) → (x : A) → all-leq t x → sorted-bt2bst t s <=T x

sorted-bt2bst lf _ = slf
sorted-bt2bst (nd x l r) ((pl₁ , pl₂) , (pr₁ , pr₂)) = snd x (sorted-bt2bst l pl₂) (sorted-bt2bst r pr₂) (all-geq-bt2bst l pl₂ x pl₁) (all-leq-bt2bst r pr₂ x pr₁)

all-geq-bt2bst lf s x _ = tt
all-geq-bt2bst (nd x l r) ((pl₁ , pl₂) , (pr₁ , pr₂)) a (p₁ , p₂ , p₃) = p₁ , all-geq-bt2bst r pr₂ a p₃

all-leq-bt2bst lf s x _ = tt
all-leq-bt2bst (nd x l r) ((pl₁ , pl₂) , (pr₁ , pr₂)) a (p₁ , p₂ , p₃) = p₁ , all-leq-bt2bst l pl₂ a p₂

{-
Exercise: Define bounded binary search trees with an insertion function in Agda.
How can we define a type of unbounded binary search trees from the type of bounded ones?
Write functions converting between the different kinds of binary trees discussed above.
-}
