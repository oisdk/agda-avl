\documentclass{article}
\usepackage{amssymb}
\usepackage{turnstile}
\usepackage{bbm}
\usepackage[greek, english]{babel}
\usepackage{MnSymbol}
\usepackage{ucs}
\usepackage{graphicx}
\usepackage{fdsymbol}

\DeclareUnicodeCharacter{9034}{\ensuremath{0}}
\DeclareUnicodeCharacter{8343}{\ensuremath{_l}}
\DeclareUnicodeCharacter{7523}{\ensuremath{_r}}
\DeclareUnicodeCharacter{9661}{\ensuremath{\mathbin{\rotatebox[origin=c]{180}{$\dotminus$}}}}
\DeclareUnicodeCharacter{9727}{\ensuremath{\mathbin{\rotatebox[origin=c]{225}{$\dotminus$}}}}
\DeclareUnicodeCharacter{9722}{\ensuremath{\mathbin{\rotatebox[origin=c]{135}{$\dotminus$}}}}
\DeclareUnicodeCharacter{9041}{\ensuremath{1}}
\DeclareUnicodeCharacter{9014}{\ensuremath{{}^{⌈⌉}_{⌊⌋}}}
\DeclareUnicodeCharacter{737}{\ensuremath{^{l}}}
\DeclareUnicodeCharacter{691}{\ensuremath{^{r}}}
\DeclareUnicodeCharacter{8405}{\ensuremath{\minusrdots}}
\DeclareUnicodeCharacter{8404}{\ensuremath{\minusfdots}}

\usepackage[utf8x]{inputenc}
\usepackage{autofe}
\usepackage{agda}
\usepackage{forest}
\usepackage{cite}
\begin{document}
\title{AVL Trees}
\author{D Oisín Kidney}
\maketitle
\abstract{
  This is a verified implementation of AVL trees in Agda, taking ideas
  primarily from Conor McBride's paper ``How to Keep Your Neighbours in
  Order'' \cite{mcbride_how_2014} and the Agda standard library
  \cite{danielsson_agda_2018}.
}
\tableofcontents
\section{Introduction}
First, some imports.
\begin{code}
{-# OPTIONS --without-K #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level using (Lift; lift; _⊔_; lower)
open import Data.Nat as ℕ using (ℕ; suc; zero; pred)
open import Data.Product
open import Data.Unit
open import Data.Maybe
open import Function
open import Data.Bool
open import Data.Empty
\end{code}

Next, we declare a module: the entirety of the following code is
parameterized over the \emph{key} type, and a strict total order on
that key.
\begin{code}
module AVL
  {k r} (Key : Set k)
  {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

  open IsStrictTotalOrder isStrictTotalOrder
\end{code}
\section{Bounded}
The basic idea of the verified implementation is to store in each leaf
a proof that the upper and lower bounds of the trees to its left and
right are ordered appropriately.

Accordingly, the tree type itself will have to have the upper and
lower bounds in its indices. But what are the upper and lower bounds
of a tree with no neighbours? To describe this case, we add lower and
upper bounds to our key type.
\begin{code}
  module Bounded where

    infix 5 [_]

    data [∙] : Set k where
      ⌊⌋ ⌈⌉  : [∙]
      [_]    : (k : Key) → [∙]
\end{code}

This type itself admits an ordering relation.
\begin{code}
    infix 4 _[<]_

    _[<]_ : [∙] → [∙] → Set r
    ⌊⌋     [<] ⌊⌋     = Lift r ⊥
    ⌊⌋     [<] ⌈⌉     = Lift r ⊤
    ⌊⌋     [<] [ _ ]  = Lift r ⊤
    ⌈⌉     [<] _      = Lift r ⊥
    [ _ ]  [<] ⌊⌋     = Lift r ⊥
    [ _ ]  [<] ⌈⌉     = Lift r ⊤
    [ x ]  [<] [ y ]  = x < y
\end{code}

Finally, we can describe a value as being ``in bounds'' like so.
\begin{code}
    infix 4 _<_<_

    _<_<_ : [∙] → Key → [∙] → Set r
    l < x < u = l [<] [ x ] × [ x ] [<] u
\end{code}
\section{Balance}
To describe the balance of the tree, we use the following type:
\begin{code}
    data ⟨_⊔_⟩≡_ : ℕ → ℕ → ℕ → Set where
      ◿   : ∀ {n} → ⟨ suc  n ⊔      n ⟩≡ suc  n
      ▽   : ∀ {n} → ⟨      n ⊔      n ⟩≡      n
      ◺   : ∀ {n} → ⟨      n ⊔ suc  n ⟩≡ suc  n
\end{code}
The tree can be either left- or right-heavy (by one), or even. The
indices of the type are phrased as a proof:
\begin{equation}
  max(x,y) = z
\end{equation}
The height of a tree is the maximum height of its two subtrees, plus
one. Storing a proof of the maximum in this way will prove useful
later.

We will also need some combinators for balance:
\begin{code}
    ⃕ : ∀ {x y z} → ⟨ x ⊔ y ⟩≡ z → ⟨ z ⊔ x ⟩≡ z
    ⃕  ◿   = ▽
    ⃕  ▽   = ▽
    ⃕  ◺   = ◿

    ⃔ : ∀ {x y z} → ⟨ x ⊔ y ⟩≡ z → ⟨ y ⊔ z ⟩≡ z
    ⃔  ◿   = ◺
    ⃔  ▽   = ▽
    ⃔  ◺   = ▽
\end{code}
\section{The Tree Type}
The type itself is indexed by the lower and upper bounds, some
value to store with the keys, and a height. In using the balance type
defined earlier, we ensure that the children of a node cannot differ
in height by more than 1. The bounds proofs also ensure that the tree
must be ordered correctly.
\begin{code}
    data Tree  {v}
               (V : Key → Set v)
               (l u : [∙]) : ℕ →
               Set (k ⊔ v ⊔ r) where
      leaf  : (l<u : l [<] u) → Tree V l u 0
      node  : ∀  {h lh rh}
                 (k : Key)
                 (v : V k)
                 (bl : ⟨ lh ⊔ rh ⟩≡ h)
                 (lk : Tree V l [ k ] lh)
                 (ku : Tree V [ k ] u rh) →
                 Tree V l u (suc h)
\end{code}
\section{Rotations}
AVL trees are rebalanced by rotations: if, after an insert or deletion,
the balance invariant has been violated, one of these rotations is
performed as correction.

Before we implement the rotations, we need a type to describe a tree
whose height may have changed:
\begin{code}
    open import Data.Fin as Fin using (Fin)

    infixl 6 _⊕_
    _⊕_ : Fin 2 → ℕ → ℕ
    Fin.zero ⊕ n = n
    Fin.suc Fin.zero ⊕ n = suc n
    Fin.suc (Fin.suc ()) ⊕ n

    Inserted  : ∀ {v} (V : Key → Set v) (l u : [∙]) (n : ℕ)
              → Set (k ⊔ v ⊔ r)
    Inserted V l u n = ∃[ i ] Tree V l u (i ⊕ n)

    pattern 0+_ tr = Fin.zero , tr
    pattern 1+_ tr = Fin.suc Fin.zero , tr
\end{code}
\subsection{Right Rotation}
When the left subtree becomes too heavy, we rotate the tree to the
right.
\begin{code}
    rotʳ  : ∀ {lb ub rh v} {V : Key → Set v}
          → (k : Key)
          → V k
          → Tree V lb [ k ] (suc (suc rh))
          → Tree V [ k ] ub rh
          → Inserted V lb ub (suc (suc rh))
\end{code}
This rotation comes in two varieties: single and double. Single
rotation can be seen in figure~\ref{rightsingle}.
\begin{figure}[h]
  \centering
  \begin{forest}
      [ $x$, AgdaInductiveConstructor
            [ $y$, AgdaInductiveConstructor
                  [ $a$, AgdaField ]
                  [ $b$, AgdaField ]]
            [ $c$, AgdaField ]]
  \end{forest}
  \raisebox{1cm}{
    \begin{tikzpicture}
      \draw[->] (0,0) -- (1,0);
    \end{tikzpicture}
  }
  \begin{forest}
      [ $y$, AgdaInductiveConstructor
            [ $a$, AgdaField ]
            [ $x$, AgdaInductiveConstructor
                  [ $b$, AgdaField ]
                  [ $c$, AgdaField ]]]
  \end{forest}
  \caption{Single right-rotation}
  \label{rightsingle}
\end{figure}
\begin{code}
    rotʳ x xv (node y yv ◿ a b) c =
      0+ (node y yv ▽ a (node x xv ▽  b c))
    rotʳ x xv (node y yv ▽ a b) c =
      1+ (node y yv ◺ a (node x xv ◿  b c))
\end{code}
And double rotation in figure~\ref{rightdouble}.
\begin{figure}[h]
  \centering
  \begin{forest}
      [ $x$, AgdaInductiveConstructor
            [ $y$, AgdaInductiveConstructor
                  [ $a$, AgdaField ]
                  [ $z$, AgdaInductiveConstructor
                        [ $b$, AgdaField ]
                        [ $c$, AgdaField ]]]
            [ $d$, AgdaField ]]
  \end{forest}
  \raisebox{1cm}{
    \begin{tikzpicture}
      \draw[->] (0,0) -- (1,0);
    \end{tikzpicture}
  }
  \begin{forest}
      [ $z$, AgdaInductiveConstructor
            [ $y$, AgdaInductiveConstructor
                  [ $a$, AgdaField ]
                  [ $b$, AgdaField ]]
            [ $x$, AgdaInductiveConstructor
                  [ $c$, AgdaField ]
                  [ $d$, AgdaField ]]]
  \end{forest}
  \caption{Double right-rotation}
  \label{rightdouble}
\end{figure}
\begin{code}
    rotʳ x xv (node y yv ◺  a (node z zv bl b c)) d =
      0+ (node z zv ▽ (node y yv (⃕ bl) a b) (node x xv (⃔ bl) c d))
\end{code}
\subsection{Left Rotation}
Left-rotation is essentially the inverse of right.
\begin{code}
    rotˡ  : ∀ {lb ub lh v} {V : Key → Set v}
          → (k : Key)
          → V k
          → Tree V lb [ k ] lh
          → Tree V [ k ] ub (suc (suc lh))
          → Inserted V lb ub (suc (suc lh))
\end{code}
\begin{figure}[h!]
  \centering
  \begin{forest}
    [ $x$, AgdaInductiveConstructor
           [ $c$, AgdaField ]
           [ $y$, AgdaInductiveConstructor
                  [ $b$, AgdaField ]
                  [ $a$, AgdaField ]]]
  \end{forest}
  \raisebox{1cm}{
    \begin{tikzpicture}
      \draw[->] (0,0) -- (1,0);
    \end{tikzpicture}
  }
  \begin{forest}
    [ $y$, AgdaInductiveConstructor
           [ $x$, AgdaInductiveConstructor
                  [ $c$, AgdaField ]
                  [ $b$, AgdaField ]]
           [ $a$, AgdaField ]]
  \end{forest}
  \caption{Single left-rotation}
  \label{leftsingle}
\end{figure}
Single (seen in figure~\ref{leftsingle}).
\begin{code}
    rotˡ x xv c (node y yv ◺ b a) =
      0+ (node y yv ▽ (node x xv ▽ c b) a)
    rotˡ x xv c (node y yv ▽ b a) =
      1+ (node y yv ◿ (node x xv ◺ c b) a)
\end{code}
\begin{figure}[h!]
  \centering
  \begin{forest}
    [ $x$, AgdaInductiveConstructor
          [ $d$, AgdaField ]
          [ $y$, AgdaInductiveConstructor
                [ $z$, AgdaInductiveConstructor
                      [ $c$, AgdaField ]
                      [ $b$, AgdaField ]]
                [ $a$, AgdaField ]]]
  \end{forest}
  \raisebox{1cm}{
    \begin{tikzpicture}
      \draw[->] (0,0) -- (1,0);
    \end{tikzpicture}
  }
  \begin{forest}
    [ $z$, AgdaInductiveConstructor
          [ $x$, AgdaInductiveConstructor
                [ $d$, AgdaField ]
                [ $c$, AgdaField ]]
          [ $y$, AgdaInductiveConstructor
                [ $b$, AgdaField ]
                [ $a$, AgdaField ]]
    ]
  \end{forest}
  \caption{Double left-rotation}
  \label{leftdouble}
\end{figure}
and double (figure~\ref{leftdouble}):
\begin{code}
    rotˡ x xv d (node y yv  ◿  (node z zv bl c b) a) =
      0+ (node z zv ▽ (node x xv (⃕ bl) d c) (node y yv (⃔ bl) b a))
\end{code}
\section{Insertion}
After the rotations, insertion is relatively easy. We allow the caller
to supply a combining function.
\begin{code}
    insert   : ∀ {l u h v} {V : Key → Set v} (k : Key)
             → V k
             → (V k → V k → V k)
             → Tree V l u h
             → l < k < u
             → Inserted V l u h
    insert v vc f (leaf l<u) (l , u) = 1+ (node v vc ▽ (leaf l) (leaf u))
    insert v vc f (node k kc bl tl tr) prf with compare v k
    insert v vc f (node k kc bl tl tr) (l , _)
        | tri< a _ _ with insert v vc f tl (l , a)
    ... | 0+ tl′ = 0+ (node k kc bl tl′ tr)
    ... | 1+ tl′ with bl
    ... | ◿ = rotʳ k kc tl′ tr
    ... | ▽ = 1+  (node k kc  ◿  tl′ tr)
    ... | ◺ = 0+  (node k kc  ▽  tl′ tr)
    insert v vc f (node k kc bl tl tr) _
        | tri≈ _ refl _ = 0+ (node k (f vc kc) bl tl tr)
    insert v vc f (node k kc bl tl tr) (_ , u)
        | tri> _ _ c with insert v vc f tr (c , u)
    ... | 0+ tr′ = 0+ (node k kc bl tl tr′)
    ... | 1+ tr′ with bl
    ... | ◿ = 0+  (node k kc  ▽  tl tr′)
    ... | ▽ = 1+  (node k kc  ◺  tl tr′)
    ... | ◺ = rotˡ k kc tl tr′
\end{code}
\section{Lookup}
Lookup is also very simple. No invariants are needed here.
\begin{code}
    lookup  : (k : Key)
            → ∀ {l u s v} {V : Key → Set v}
            → Tree V l u s
            → Maybe (V k)
    lookup k (leaf l<u) = nothing
    lookup k (node v vc _ tl tr) with compare k v
    ... | tri< _ _ _     = lookup k tl
    ... | tri≈ _ refl _  = just vc
    ... | tri> _ _ _     = lookup k tr
\end{code}
\section{Deletion}
Deletion is by far the most complex operation out of the three
provided here. For deletion from a normal BST, you go to the node
where the desired value is, perform an ``uncons'' operation on the
right subtree, and use that to rebuild and rebalance the tree.

\subsection{Uncons}
First then, we need to define ``uncons''. We'll use a custom type as
the return type from our uncons function, which stores the minimum
element from the tree, and the rest of the tree:
\begin{code}
    data Deleted {v} (V : Key → Set v) (lb ub : [∙]) : ℕ → Set (k ⊔ v ⊔ r) where
      _−0 : ∀ {n} → Tree V lb ub n → Deleted V lb ub n
      _−1 : ∀ {n} → Tree V lb ub n → Deleted V lb ub (suc n)

    deleted : ∀ {v lb ub n} {V : Key → Set v} → Inserted V lb ub n → Deleted V lb ub (suc n)
    deleted (0+ snd) = snd −1
    deleted (1+ snd) = snd −0
    deleted (Fin.suc (Fin.suc ()) , snd)

    record Cons {v}
                (V : Key → Set v)
                (lb ub : [∙])
                (h : ℕ) : Set (k ⊔ v ⊔ r) where
      constructor cons
      field
        head  : Key
        val   : V head
        l<u   : lb [<] [ head ]
        tail  : Inserted V [ head ] ub h
\end{code}
You'll notice it also stores a proof that the extracted element
preserves the lower bound.

The uncons function itself is written in a continuation-passing style.
\begin{code}
    uncons  : ∀ {lb ub h lh rh v} {V : Key → Set v}
            → (k : Key)
            → V k
            → ⟨ lh ⊔ rh ⟩≡ h
            → Tree V lb [ k ] lh
            → Tree V [ k ] ub rh
            → Cons V lb ub (h)
    uncons k v bl tl tr = go k v bl tl tr id
      where
      go  : ∀ {lb ub h lh rh v ub′ h′} {V : Key → Set v}
          → (k : Key)
          → V k
          → ⟨ lh ⊔ rh ⟩≡ h
          → Tree V lb [ k ] lh
          → Tree V [ k ] ub rh
          → (∀  {lb′} →
                Inserted V [ lb′ ] ub   (h) →
                Inserted V [ lb′ ] ub′  (h′))
          → Cons V lb ub′ (h′)
      go k v ▽ (leaf l<u) tr c = cons k v l<u (c (0+ tr))
      go k v ▽ (node kₗ vₗ blₗ tlₗ trₗ) tr c = go kₗ vₗ blₗ tlₗ trₗ
        λ  {  (0+ tl′) → c (1+ node k v ◺  tl′ tr)
           ;  (1+ tl′) → c (1+ node k v ▽  tl′ tr) }
      go k v ◺ (leaf l<u) tr c = cons k v l<u (c (0+ tr))
      go k v ◺ (node kₗ vₗ blₗ tlₗ trₗ) tr c = go kₗ vₗ blₗ tlₗ trₗ
        λ  {  (0+ tl′) → c (rotˡ k v tl′ tr)
           ;  (1+ tl′) → c (1+ node k v ◺ tl′ tr) }
      go k v ◿ (node kₗ vₗ blₗ tlₗ trₗ) tr c = go kₗ vₗ blₗ tlₗ trₗ
        λ  {  (0+ tl′) → c (0+ node k v ▽  tl′ tr)
           ;  (1+ tl′) → c (1+ node k v ◿  tl′ tr)}
\end{code}
\subsection{Widening}
To join the two subtrees together after a deletion operation, we need
to weaken (or ext) the bounds of the left tree. This is an
$\mathcal{O}(\log n)$ operation.

For the exting, we'll need some properties on orderings:
\begin{code}
    x≮⌊⌋ : ∀ {x} → x [<] ⌊⌋ → Lift r ⊥
    x≮⌊⌋ {⌊⌋}      = lift ∘ lower
    x≮⌊⌋ {⌈⌉}      = lift ∘ lower
    x≮⌊⌋ {[ _ ]}  = lift ∘ lower

    [<]-trans : ∀ x {y z} → x [<] y → y [<] z → x [<] z
    [<]-trans ⌊⌋      {y}      {⌊⌋}      _    y<z  = x≮⌊⌋ {x = y} y<z
    [<]-trans ⌊⌋      {_}      {⌈⌉}      _    _    = _
    [<]-trans ⌊⌋      {_}      {[ _ ]}  _    _    = _
    [<]-trans ⌈⌉      {_}      {_}      (lift ()) _
    [<]-trans [ _ ]  {y}      {⌊⌋}      _    y<z  = x≮⌊⌋ {x = y} y<z
    [<]-trans [ _ ]  {_}      {⌈⌉}      _    _    = _
    [<]-trans [ _ ]  {⌊⌋}      {[ _ ]}  (lift ()) _
    [<]-trans [ _ ]  {⌈⌉}      {[ _ ]}  _ (lift ())
    [<]-trans [ x ]  {[ y ]}  {[ z ]}  x<y  y<z  =
      IsStrictTotalOrder.trans isStrictTotalOrder x<y y<z
\end{code}
Finally, the ext function itself simply walks down the right branch
of the tree until it hits a leaf.
\begin{code}
    ext : ∀ {lb ub ub′ h v} {V : Key → Set v}
         → ub [<] ub′
         → Tree V lb ub h
         → Tree V lb ub′ h
    ext {lb} ub<ub′ (leaf l<u) = leaf ([<]-trans lb l<u ub<ub′)
    ext ub<ub′ (node k v bl tl tr) = node k v bl tl (ext ub<ub′ tr)
\end{code}
\subsection{Full Deletion}
The deletion function is by no means simple, but it does maintain the
correct complexity bounds.
\begin{code}
    join : ∀ {lb ub lh rh h v k} {V : Key → Set v}
         → Tree V [ k ] ub rh
         → ⟨ lh ⊔ rh ⟩≡ h
         → Tree V lb [ k ] lh
         → Deleted V lb ub (suc h)
    join (leaf k<ub) ◿ tl = ext k<ub tl −1
    join {lb} (leaf k<ub) ▽ (leaf lb<k) = leaf ([<]-trans lb lb<k k<ub) −1
    join (node kᵣ vᵣ bᵣ tlᵣ trᵣ) b  tl with uncons kᵣ vᵣ bᵣ tlᵣ trᵣ
    ... | cons k′ v′ l<u (1+ tr′)  = node k′ v′ b  (ext l<u tl) tr′ −0
    ... | cons k′ v′ l<u (0+ tr′) with b
    ... | ◿ = deleted (rotʳ k′ v′ (ext l<u tl) tr′)
    ... | ▽ = node k′ v′ ◿  (ext l<u tl) tr′ −0
    ... | ◺ = node k′ v′ ▽  (ext l<u tl) tr′ −1

    delete : ∀ {lb ub h v} {V : Key → Set v}
           → (k : Key)
           → Tree V lb ub h
           → Deleted V lb ub h
    delete x (leaf l<u) = leaf l<u −0
    delete x (node y yv b l r) with compare x y
    delete x (node .x yv b l r) | tri≈ ¬a refl ¬c = join r b l
    delete x (node y yv b l r) | tri< a ¬b ¬c with delete x l
    ... | l′ −0 = node y yv b l′ r −0
    ... | l′ −1 with b
    ... | ◿ = node y yv ▽ l′ r −1
    ... | ▽ = node y yv ◺ l′ r −0
    ... | ◺ = deleted (rotˡ y yv l′ r)
    delete x (node y yv b l r) | tri> ¬a ¬b c with delete x r
    ... | r′ −0 = node y yv b l r′ −0
    ... | r′ −1 with b
    ... | ◿ = deleted (rotʳ y yv l r′)
    ... | ▽ = node y yv ◿ l r′ −0
    ... | ◺ = node y yv ▽ l r′ −1
\end{code}
\section{Alteration}
\begin{code}
    -- alter : ∀ {lb ub h v} {V : Key → Set v}
    --       → (k : Key)
    --       → (Maybe (V k) → Maybe (V k))
    --       → Tree V lb ub h
    --       → lb < k < ub
    --       → Altered V lb ub h
--     alter x f (leaf l<u) (l , u) with f nothing
--     alter x f (leaf l<u) (l , u) | just yv = ↑ (node x yv ▽ (leaf l) (leaf u))
--     alter x f (leaf l<u) (l , u) | nothing = ⟨ leaf l<u ⟩
--     alter x f (node y yv bl tl tr) (l , u) with compare x y
--     alter x f (node .x xv bl tl tr) (l , u) | tri≈ ¬a refl ¬c with f (just xv)
--     alter x f (node .x xv bl tl tr) (l , u) | tri≈ ¬a refl ¬c | just yv = ⟨ node x yv bl tl tr ⟩
--     alter x f (node .x xv bl tl tr) (l , u) | tri≈ ¬a refl ¬c | nothing = fromDeleted (join tr bl tl)
--     alter x f (node y yv bl tl tr) (l , u) | tri< a ¬b ¬c with alter x f tl (l , a)
--     alter x f (node y yv bl tl tr) (l , u) | tri< a ¬b ¬c | ↑ tl′ with bl
--     alter x f (node y yv bl tl tr) (l , u) | tri< a ¬b ¬c | ↑ tl′ | ◿ = fromInserted↑ (rotʳ y yv tl′ tr)
--     alter x f (node y yv bl tl tr) (l , u) | tri< a ¬b ¬c | ↑ tl′ | ▽ = ↑ (node y yv ◿ tl′ tr)
--     alter x f (node y yv bl tl tr) (l , u) | tri< a ¬b ¬c | ↑ tl′ | ◺ = ⟨ node y yv ▽ tl′ tr ⟩
--     alter x f (node y yv bl tl tr) (l , u) | tri< a ¬b ¬c | ⟨ tl′ ⟩ = ⟨ node y yv bl tl′ tr ⟩
--     alter x f (node y yv bl tl tr) (l , u) | tri< a ¬b ¬c | ↓ tl′ with bl
--     alter x f (node y yv bl tl tr) (l , u) | tri< a ¬b ¬c | ↓ tl′ | ◿ = ↓ (node y yv ▽ tl′ tr)
--     alter x f (node y yv bl tl tr) (l , u) | tri< a ¬b ¬c | ↓ tl′ | ▽ = ⟨ node y yv ◺ tl′ tr ⟩
--     alter x f (node y yv bl tl tr) (l , u) | tri< a ¬b ¬c | ↓ tl′ | ◺ = fromInserted↓ (rotˡ y yv tl′ tr)
--     alter x f (node y yv bl tl tr) (l , u) | tri> ¬a ¬b c with alter x f tr (c , u)
--     alter x f (node y yv bl tl tr) (l , u) | tri> ¬a ¬b c | ↑ tr′ with bl
--     alter x f (node y yv bl tl tr) (l , u) | tri> ¬a ¬b c | ↑ tr′ | ◿ = ⟨ node y yv  ▽  tl tr′ ⟩
--     alter x f (node y yv bl tl tr) (l , u) | tri> ¬a ¬b c | ↑ tr′ | ▽ = ↑ (node y yv  ◺  tl tr′)
--     alter x f (node y yv bl tl tr) (l , u) | tri> ¬a ¬b c | ↑ tr′ | ◺ = fromInserted↑ (rotˡ y yv tl tr′)
--     alter x f (node y yv bl tl tr) (l , u) | tri> ¬a ¬b c | ⟨ tr′ ⟩ = ⟨ node y yv bl tl tr′ ⟩
--     alter x f (node y yv bl tl tr) (l , u) | tri> ¬a ¬b c | ↓ tr′ with bl
--     alter x f (node y yv bl tl tr) (l , u) | tri> ¬a ¬b c | ↓ tr′ | ◿ = fromInserted↓ (rotʳ y yv tl tr′)
--     alter x f (node y yv bl tl tr) (l , u) | tri> ¬a ¬b c | ↓ tr′ | ▽ = ⟨ node y yv ◿  tl tr′ ⟩
--     alter x f (node y yv bl tl tr) (l , u) | tri> ¬a ¬b c | ↓ tr′ | ◺ = ↓ (node y yv ▽  tl tr′)

\end{code}
\section{Packaging}
Users don't need to be exposed to the indices on the full tree type:
here, we package it in thee forms.
\subsection{Dependent Map}
\begin{code}
  module DependantMap where
    data Map {v} (V : Key → Set v) : Set (k ⊔ v ⊔ r) where
      tree  : ∀ {h}
            → Bounded.Tree V Bounded.⌊⌋ Bounded.⌈⌉ h
            → Map V

    insertWith  : ∀ {v} {V : Key → Set v} (k : Key)
                → V k
                → (V k → V k → V k)
                → Map V
                → Map V
    insertWith k v f (tree tr) = tree (proj₂ (Bounded.insert k v f tr (lift tt , lift tt)))

    insert : ∀  {v}
                {V : Key → Set v}
                (k : Key) →
                V k →
                Map V →
                Map V
    insert k v = insertWith k v const

    lookup  : (k : Key)
            → ∀ {v} {V : Key → Set v}
            → Map V
            → Maybe (V k)
    lookup k (tree tr) = Bounded.lookup k tr

    delete  : (k : Key)
            → ∀ {v} {V : Key → Set v}
            → Map V
            → Map V
    delete k (tree tr) with Bounded.delete k tr
    ... | tr′ Bounded.−0 = tree tr′
    ... | tr′ Bounded.−1 = tree tr′
\end{code}
\subsection{Non-Dependent (Simple) Map}
\begin{code}
  module Map where
    data Map {v} (V : Set v) : Set (k ⊔ v ⊔ r) where
      tree  : ∀ {h}
            → Bounded.Tree (const V) Bounded.⌊⌋ Bounded.⌈⌉ h
            → Map V

    insertWith  : ∀ {v} {V : Set v} (k : Key)
                → V
                → (V → V → V)
                → Map V
                → Map V
    insertWith k v f (tree tr) = tree (proj₂ (Bounded.insert k v f tr (lift tt , lift tt)))

    empty : ∀ {v} {V : Set v} → Map V
    empty = tree (Bounded.leaf (lift tt))

    insert : ∀ {v} {V : Set v} (k : Key) → V → Map V → Map V
    insert k v = insertWith k v const

    lookup : (k : Key) → ∀ {v} {V : Set v} → Map V → Maybe V
    lookup k (tree tr) = Bounded.lookup k tr

    delete : (k : Key) → ∀ {v} {V : Set v} → Map V → Map V
    delete k (tree tr) with Bounded.delete k tr
    ... | tr′ Bounded.−0 = tree tr′
    ... | tr′ Bounded.−1 = tree tr′
\end{code}
\subsection{Set}
Note that we can't call the type itself ``Set'', as that's a reserved
word in Agda.
\begin{code}
  module Sets where
    data ⟨Set⟩ : Set (k ⊔ r) where
      tree  : ∀ {h}
            → Bounded.Tree (const ⊤) Bounded.⌊⌋ Bounded.⌈⌉ h
            → ⟨Set⟩

    insert : Key → ⟨Set⟩ → ⟨Set⟩
    insert k (tree tr) = tree (proj₂ (Bounded.insert k tt const tr (lift tt , lift tt)))

    member : Key → ⟨Set⟩ → Bool
    member k (tree tr) = is-just (Bounded.lookup k tr)

    delete : (k : Key) → ⟨Set⟩ → ⟨Set⟩
    delete k (tree tr) with Bounded.delete k tr
    ... | tr′ Bounded.−0 = tree tr′
    ... | tr′ Bounded.−1 = tree tr′
\end{code}
\bibliographystyle{IEEEtranS}
\bibliography{../AVL.bib}
\end{document}
