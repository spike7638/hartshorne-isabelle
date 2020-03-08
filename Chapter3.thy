theory Chapter3
  imports Chapter2

begin
section\<open>Digression on Groups and Automorphisms\<close>
text \<open>
\begin{hartshorne}
\defn[group]. A \term{group} is a set $G$ together with a binary operation, called multiplication,
written $ab$ such that
\begin{itemize}
\item[G1] (\term{Associativity}) For all $a,b,c\in G, (ab)c = a(bc)$.
\item[G2] There exists an element $1 \in G$ such that $a \cdot 1 = 1 \cdot a = a \cdot 1 = a$ for all $a$.
\item[G3] For each $a \in G$, there exists an element $a^{-1} \in G$ such that $aa^{-1} = a^{-1}a = 1$.
\end{itemize}
The element $1$ is called the \term{identity}, or \term{unit}, element. The element $a^{-1}$ is 
called the \term{inverse} of $a.$ Note that in general the product $ab$ may be different from $ba.$
However, we say that the group $G$ is \term{abelian,} or \term{commutative,} if
G4 $\forall a, b \in G, ab = ba.$

Examples. 

1. Let $S$ be any set, and let $G$ be the set of permutations of the set $S.$
A \term{permutation} is a 1–1 mapping of a set $S$ onto $S.$ If $g_1, g_2 \in G$
are two permutations, we define $g_1 g_2 \in G$ to be the permutation obtained by 
performing first $g_2$, then $g_1$, i.e., if $x \in S$, then
$$
(g_1g_2)(x) = g_1(g_2(x)).
$$

2. Let $C$ be a configuration, and let $G$ be the set of \term{automorphisms} of $C$,
i.e., the set of those permutations of $C$ which send lines into lines. 
Again we define the product $g_1g_2$ of two automorphisms $g_1,g_2$, by performing 
$g_2$ first, and then $g_1.$ This group is written $\operatorname{Aut} C$.

\defn [homomorphism] A \term{homomorphism} $\phi: G_1 \to G_2$ of one group to another is a 
mapping of the set $G_1$ to the set $G_2$ such that $\phi(ab) = \phi(a) \phi(b)$ for each $a, b \in G_1$. 

An \term{isomorphism} of one group with another is a homomorphism which is
1–1 and onto.

\defn [subgroup]  Let $G$ be a group. A subgroup of $G$ is a non-empty subset
$H \subseteq G,$ such that for any $a,b \in H,$ $ab \in H$ and $a^{-1} \in H.$
\end{hartshorne}
 \<close>



subsection\<open>Automorphisms of the real projective plane\<close>
text \<open>\begin{hartshorne}Here we study another important example of the automorphisms of a pro-
jective plane. Recall that the real projective plane is defined as follows: A point
is given by homogeneous coordinates $(x_1 , x_2 , x_3 )$. That is, a triple of real num-
bers, not all zero, and with the convention that $(x_1 , x_2 , x_3)$ and $(\lambda x_1, \lambda x_2, \lambda x_3)$
represent the same point, for any $\lambda \ne 0$, $\lambda \in \Bbb R.$ 
A \term{line} is the set of points which satisfy an equation of the form 

\begin{equation*}
a_1 x_1 + a_2 x_2 + a_3 x_3 = 0,
\end{equation*}

$a_i \in \Bbb R,$ not all zero. \end{hartshorne}\<close>

subsubsection\<open>Brief review of matrices\<close>
text \<open>\begin{hartshorne}
A $n \times n$ \term{matrix} of real numbers is a collection of $n^2$ real numbers, indexed
by two indices, say $i$, $j$, each of which may take values from 1 to $n$. Hence
$A = {a_{11}, a_{12}, \ldots , a_{21}, a_{22}, \ldots , a_{n1}, a_{n2}, \ldots , a_{nn}}.$ The matrix is
usually written in a square:
$$
\begin{pmatrix}
a_{11} & a_{12} & \hdots & a_{1n} \\
a_{21} & a_{22} & \hdots & a_{2n} \\
\vdots & \vdots & \ddots & \vdots \\
a_{n1} & a_{n2} & \hdots & a_{nn}
\end{pmatrix} 
$$
Here the first subscript determines the row, and the second subscript determines
the column.

The product of two matrices $A = (a_{ij})$ and $B = (b_{ij})$ (both of order $n$) is
defined to be

\begin{equation*}
  A \cdot B = C
\end{equation*}

where $C = (c_{ij})$ and

\begin{equation*}
  c_{ij} = \sum_{k=1}^n a_{ik} b_{kj}.
\end{equation*}

\[
\begin{pmatrix}
a_{i1} & \hdots & a_{in} \\
\end{pmatrix}
\begin{pmatrix}
b_{1j} \\
\vdots \\
b_{nj} \\
\end{pmatrix}
= ( c_{ij} )
\]


\[c_{ij} = a_{i1}b_{1j} + a_{i2}b_{2j} + \hdots  + a_{in}b_{nj}\]

There is also a function \textbf{determinant}, from the set of $n \times n$ matrices to $\mathbb{R}$,
which is characterized by the following two properties:

\textbf{D1} \textit{If A, B are two matrices}

\[ det(A \cdot B) = det A \cdot det B\]

\textbf{D2} \textit{For each $a \in R$, let $C(a) = \ldots $}

Note incidentally that the identity matrix $I = C(1)$ behaves as a multiplicative identity. 
One can prove the following facts:
\begin{enumerate}
\item $(A \cdot B) \cdot C = A \cdot (B \cdot C)$, i.e. multiplication of matrices is associative. 
(In general it is not commutative.)

\item A matrix $A$ has a multiplicative inverse $A^{-1}$
if and only if $det A \neq 0$.

Hence the set of $n \times n$ matrices $A$ with $\det A \neq 0$ forms a group under multiplication, 
denoted by GL$(n, \mathbb{R})$. 
\item Let $A = (a_{ij})$ be a matrix, and consider the set of simultaneous linear
equations
\begin{align}
a_{11}x_1 + a_{12}x_2 + \hdots + a_{1n}x_n &= b_1 \\
a_{21}x_1 + a_{22}x_2 + \hdots + a_{2n}x_n &= b_2 \\
\vdots &= \vdots\\
a_{n1}x_1 + a_{n2}x_2 + \hdots + a_{nn}x_n &= b_n
\end{align}
If $\det A \neq 0$, then this set of equations has a solution. Conversely, if this
set of equations has a solution for all possible choices of $b_1, \hdots, b_n$ then
$\det A \neq 0$.
\end{enumerate}
For proofs of these statements, refer to any book on algebra. We will take
them for granted, and use them without comment in the rest of the course. One
can prove easily that 3 follows from 1 and 2. Because to say $x_1, \hdots, x_n$ are a
solution of that system of linear equations is the same as saying that

\[
A \cdot
\begin{pmatrix}
x_1 \\
x_2 \\
\vdots \\
x_n \\
\end{pmatrix}
=
\begin{pmatrix}
b_1 \\
b_2 \\
\vdots \\
b_n \\
\end{pmatrix}
\]
Now let $A = (a_{ij})$ be a $3 \times 3$ matrix of real numbers, and let $\pi$ be the real
projective plane, with homogeneous coordinates $x_1, x_2, x_3$. We define a transformation $T_A$ of $\pi$ as follows: 
The point $(x_1, x_2, x_3)$ goes into the point
\[T_A(x_1, x_2, x_3) = (x_1', x_2', x_3')\]
where
\[x_1' = a_{11}x_1 + a_{12}x_2 + a_{13}x_3\]
\[x_2' = a_{21}x_1 + a_{22}x_2 + a_{23}x_3\]
\[x_3' = a_{31}x_1 + a_{32}x_2 + a_{33}x_3\]
\end{hartshorne}
\<close>

(*
CONTINUES WITH DOT-PRODUCT DEFINITION OF MATRIX MULTIPLICATION
*)

end





