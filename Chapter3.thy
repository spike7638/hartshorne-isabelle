theory Chapter3
  imports Chapter2

begin
section\<open>Digression on Groups and Automorphisms\<close>
text \<open>\defn[group]. A \term{group} is a set $G$ together with a binary operation, called multiplication,
written $ab$ such that
\begin{itemize}
\item[G1] (\term{Associativity}) For all $a,b,c\in G, (ab)c = a(bc)$.
\item[G2] There exists an element $1 \in G$ such that $a \cdot 1 = 1 \cdot a = a \cdot 1 = a$ for all $a$.
\item[G3] For each $a \in G$, there exists an element $a^{-1} \in G$ such that $aa^{-1} = a^{-1}a = 1$.
\end{itemize}
The element 1 is called the \term{identity}, or \term{unit}, element. The element a−1 is called the inverse of a.
Note that in general the product ab may be different from ba. However, we say that the group G is abelian, or commutative, if
G4 Foralla,b\<in>G,ab=ba.
Examples. 1. Let S be any set, and let G be the set of permutations of the set S. A permutation is a 1–1 mapping of a set S onto S. If g1,g2 \<in> G are two permutations, we define g1g2 \<in> G to be the permutation obtained by performing first g2, then g1 (i.e. if x \<in> S,
(g1g2)(x) = g1(g2(x)).)
2. Let C be a configuration, and let G be the set of automorphisms of C, i.e. the set of those permutations of C which send lines into lines. Again we define the product g1g2 of two automorphisms g1,g2, by performing g2 first, and then g1. This group is written AutC.
Definition. A homomorphism \<phi> : G1 \<rightarrow> G2 of one group to another is a mapping of the set G1 to the set G2 such that
\<phi>(ab) = \<phi>(a)\<phi>(b)
for each a,b \<in> G1.
An isomorphism of one group with another is a homomorphism which is
1–1 and onto.
Definition. Let G be a group. A subgroup of G is a non-empty subset
H \<subseteq> G, such that for any a,b \<in> H, ab \<in> H and a−1 \<in> H.
end \<close>



subsection\<open>Automorphisms of the real projective plane\<close>
text \<open>\begin{hartshorne}Here we study another important example of the automorphisms of a pro-
jective plane. Recall that the real projective plane is defined as follows: A point
is given by homogeneous coordinates $(x_1 , x_2 , x_3 )$. That is, a triple of real num-
bers, not all zero, and with the convention that $(x_1 , x_2 , x_3)$ and $(\<lambda>x_1, \<lambda>x_2, \<lambda>x_3)$
represent the same point, for any \<lambda> 6 = 0, \<lambda> \<in> \<real>. A line is the set of points which
satisfy an equation of the form 

\begin{equation*}
a_1 x_1 + a_2 x_2 + a_3 x_3 = 0,
\end{equation*}

$a_i$ \<in> \<real>, not all zero. \end{hartshorne}\<close>

subsubsection\<open>Brief review of matrices\<close>
text \<open>A $n \times n$ \term{matrix} of real numbers is a collection of $n^2$ real numbers, indexed
by two indices, say $i$, $j$, each of which may take values from 1 to $n$. Hence
$A = {a_{11}, a_{12}, \<dots>, a_{21}, a_{22}, \<dots>, a_{n1}, a_{n2}, \<dots>, a_{nn}}. The matrix is
usually written in a square:
\begin{pmatrix}
a_{11} & a_{12} & \hdots & a_{1n} \\
a_{21} & a_{22} & \hdots & a_{2n} \\
\vdots & \vdots & \ddots & \vdots \\
a_{n1} & a_{n2} & \hdots & a_{nn}
\end{pmatrix} 

Here the first subscript determines the row, and the second subscript determines
the column.

The product of two matrices $A = (a_{ij})$ and $B = (b_{ij})$ (both of order n) is
defined to be

\begin{equation*}
  A \dot B = C
\end{equation*}

where $C = (c_{ij})% and

\begin{equation*}
  \sum_{n}^{k=1} a_{ik} b_{kj}.
\end{equation*}\<close>

(*
CONTINUES WITH DOT-PRODUCT DEFINITION OF MATRIX MULTIPLICATION
*)







