theory Chapter2
  imports Chapter1

begin

section \<open>Desargues' Theorem\<close>
text \<open>\begin{hartshorne}
One of the first main results of projective geometry is ”Desargues’ Theorem”, which states the following: [picture missing]
\prop[P5 (Desargues' Theorem)]
Let two triangles $ABC$ and $A'B'C'$ be such that the lines joining corresponding vertices, namely 
$AA'$, $BB'$, and $CC'$, pass through a point $O$. (We say that the two triangles are \term{perspective 
from $O$}.) Then the three pairs of corresponding sides intersect in three points
\begin{align*}
P &= AB \cdot A'B'\\
R &= BC \cdot B'C' \\ 
Q &= AC \cdot A'C' \\
\end{align*}
which lie on a straight line.


\end{hartshorne}\<close>

text \<open>\begin{hartshorne}
Now it is not quite right for us to call this a ``theorem,'' because it cannot be proved from our 
axioms P1–P4. However, we will show that it is true in the real projective plane (and, more 
generally, in any projective plane which can be embedded in a three-dimensional projective space).

Then we will take this statement as a further axiom, P5, of our abstract projective geometry. 
We will show by an example that P5 is not a consequence of P1–P4: namely, we will exhibit a 
geometry which satisfies P1–P4 but not P5.

\defn[Projective 3-space] A \term{projective 3-space} is a set whose elements are called 
\term{points,} together with
certain subsets called \term{lines} and certain other subsets called 
\term{planes,} which satisfies the following axioms:
\begin{itemize}
\item[S1] Two distinct points $P, Q$ lie on one and only one line $l$. 
\item [S2] Three non-collinear points 
$P, Q, R$ lie on a unique plane. 
\item[S3] A line meets a plane in at least one point.
\item[S4] Two planes have at least a line in common.
\item[S5] There exist four non-coplanar points, no three of which are collinear. 
\item [S6] Every line has at least three points.
\end{itemize}

\end{hartshorne}\<close>


locale projective_three_space_data =
  fixes meetsL :: "'point \<Rightarrow> 'line \<Rightarrow> bool"
  fixes meetsP :: "'point \<Rightarrow> 'plane \<Rightarrow> bool"

begin
    definition parallel:: "'line  \<Rightarrow> 'line \<Rightarrow> bool" (infix "||" 50)
      where "l || m \<longleftrightarrow> (l = m \<or> \<not> (\<exists> P. meetsL P l  \<and> meetsL P m))"
 
    definition collinear :: "'point  \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> bool"
      where "collinear A B C \<longleftrightarrow> (\<exists> l. meetsL A l \<and> meetsL B l \<and> meetsL C l)"

    definition coplanar :: "'point \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> bool"
      where "coplanar P Q R S \<longleftrightarrow> (\<exists>p. meetsP P p \<and> meetsP Q p \<and> meetsP R p \<and> meetsP S p)"

    definition lies_on :: "'line \<Rightarrow> 'plane \<Rightarrow> bool"
      where "lies_on l p \<longleftrightarrow> (\<forall>P. (meetsL P l \<longleftrightarrow> meetsP P p))"

  end
  value "projective_three_space_data"

  locale projective_three_space =
    projective_three_space_data meetsL meetsP
    for meetsL :: "'point \<Rightarrow> 'line \<Rightarrow> bool" and meetsP :: "'point \<Rightarrow> 'plane \<Rightarrow> bool" +
  assumes
    s1: "P \<noteq> Q \<Longrightarrow> \<exists>!l. meetsL P l \<and> meetsL Q l" and
    s2: "\<not>(collinear P Q R) \<Longrightarrow> \<exists>!p. meetsP P p \<and> meetsP Q p \<and> meetsP R p " and
    s3: "\<forall>p l. \<exists>P. meetsL P l \<and> meetsP P p" and 
    s4: "\<forall> p q. \<exists>l. lies_on l p \<and> lies_on l q" and
    s5: "\<exists>P Q R S. \<not>(coplanar P Q R S) \<and> \<not>(collinear P Q R) \<and> \<not>(collinear Q R S) \<and> \<not>(collinear P Q S) \<and> \<not>(collinear P R S)" and
    s6: "\<forall> l. \<exists> P Q R. P \<noteq> Q \<and> Q \<noteq> R \<and> P \<noteq> R \<and> meetsL P l \<and> meetsL Q l \<and> meetsL R l"
begin

lemma p7a:
  fixes P and Q and s and l
  assumes "P \<noteq> Q" and "meetsP P s" and "meetsP Q s" and "meetsL P l" and "meetsL Q l"
  shows "lies_on l s"
  sorry

lemma p7b:
  fixes p l
  assumes "\<not>(lies_on l p)"
  shows "\<exists>!P. meetsL P l \<and> meetsP P p"
  sorry

lemma p7c:
  fixes p q
  assumes "p \<noteq> q"
  shows "\<exists>!l. lies_on l p \<and> lies_on l q"
  sorry

lemma p7d:
  fixes P l
  assumes "\<not>(meetsL P l)"
  shows "\<exists>!p. meetsP P p \<and> lies_on l p"
  sorry

end

text \<open>\begin{hartshorne}
Example. By a process analogous to that of completing an affine plane to a projective plane, the 
ordinary Euclidean three-space can be completed to a projective three-space, which we call
\term{real projective three-space.} Alternatively, this same real projective three-space can be
described by homogeneous coordinates, as follows. A point is described by a quadruple
$ (x_1, x_2, x_3, x_4)$ of real numbers, not all zero, where we agree that
$ (x_1, x_2, x_3, x_4)$ and
$ (\lambda x_1, \lambda x_2, \lambda x_3, \lambda x_4)$
represent the same point, for any $\lambda \in \Bbb R, \lambda \ne 0.$ A plane is 
defined by a linear equation
\begin{align}
\sum_{i=1}^3 a_i x_i &= 0 & \text{ $a_i \in \Bbb R,$}
\end{align}
and a line is defined as the intersection of two distinct planes. The details of verification 
of the axioms are left to the reader.

Now the remarkable fact is that, although P5 is not a consequence of P1–-P4 in the projective 
plane, it is a consequence of the seemingly equally simple axioms for projective three-space.

\end{hartshorne}\<close>

text \<open>\begin{hartshorne}

\thm[2.1] Desargues’ Theorem is true in projective three-space, where we
do not necessarily assume that all the points lie in a plane. In particular, Desargues’ 
Theorem is true for any plane (which by Problem 8 is a projective plane) which lies in a 
projective three-space.

\proof
Case 1. Let us assume that the plane $\Sigma$ containing the points $A, B, C$ is 
different from the plane $\Sigma'$ containing the points $A', B', C'.$ The lines $AB$ and $A'B'$ both 
lie in the plane determined by $O,A,B$, and so they meet in a point $P.$ Similarly we see that 
$AC$ and $A'C'$ meet, and that $BC$ and $B'C'$ meet. Now the points $P,Q,R$ lie in the plane 
$\Sigma$, and also in the plane $\Sigma'.$ Hence they lie in the intersection 
$\Sigma \cap \Sigma'$, which is a line (Problem 7c).

Case 2. Suppose that $\Sigma= \Sigma',$ so that the whole configuration lies in one plane 
(call it $\Sigma$).

Pick a point $X$ which does not lie in $\Sigma$ (this exists by axiom S5). Draw lines joining $X$ 
to all the points in the diagram. Choose $D$ on $XB,$
different from $B,$ and let $D' = OD \cdot XB'.$ (Why do they meet?) Then the triangles $ADC$ 
and $A'D'C'$ are perspective from $O,$ and do not lie in the same plane. We conclude 
from Case 1 that the points
\begin{align*}
P' & =AD \cdot A'D'\\
 Q = AC \cdot A'C' \\
 R' = DC \cdot D'C'
\end{align*}
lie in a line. But these points are projected for $X$ into $P,Q,R,$ on $\Sigma$, hence $P, Q, R$ 
are collinear.
\endproof
\end{hartshorne}\<close>


text \<open>\begin{hartshorne}

Remark. The configuration of Desargues’ Theorem has a lot of symmetry. It consists of $10$ points 
and $10$ lines. Each point lies on three lines, and each line contains $3$ points. Thus it may be given
 the symbol $(10_3).$ Also, the role of the various points is not fixed. Any one of the ten points
 can be taken as the center of perspectivity of two triangles. In fact, the group of automorphisms
 of the configuration is $\Sigma_5,$ the symmetric group on 5 letters. (Consider the action of any
 automorphism on the space version of the configuration. It must permute the five
 planes $OAB,OBC,OAC,ABC,A'B'C'.$) See Problems 12, 13, 14 for details.

We will now give an example of a non-Desarguesian projective plane, that is, a plane
satisfying P1, P2, P3, P4, but not P5. This will show that P5 is not a logical consequence of P1–P4.

\defn. A \term{configuration} is a set, whose elements are called ``points'', and a collection of
 subsets, called ``lines'', which satisfies the following axiom:

C1. Two distinct points lie on at most one line.

It follows that two distinct lines have at most one point in common.
\end{hartshorne}\<close>

text \<open>\begin{hartshorne}
Examples. Any affine plane or projective plane is a configuration. Any set of ``points'' 
and no lines is a configuration. The collection of $10$ points and $10$ lines 
which occurs in Desargues’ Theorem is a configuration.

Let $\pi_0$ be a configuration. We will now define the free projective plane generated by $\pi_0.$

Let $\pi_1$ be the new configuration defined as follows: 
\begin{itemize}
\item The points of $\pi_1$ are the points of $\pi_0.$
\item
The lines of $\pi_1$ are the lines of $\pi_0$, plus, for each pair of points $P_1, P_2 \in \pi_0$ not on a line,
 a new line $\{P1, P2\}$.
\end{itemize}

Then $\pi_1$ has the property

a) Every two distinct points lie on a line.

Construct $\pi_2$ from $\pi_1$ as follows. 

\begin{itemize}
\item
The points of $\pi_2$ are the points of $\pi_1,$ plus, for each pair of
 lines $l_1,l_2$ of $\pi_1$ which do not meet, a new point $l1 \cdot l2.$ 
\item 
The lines of $\pi_2$ 
are the lines of $\pi_1,$
 extended by their new points, e.g. the point $l_1 \cdot l_2$ lies on the extensions of the lines $l_1,l_2.$
\end{itemize}

Then $\pi_2$ has the property

b) Every pair of distinct lines meets in a point,

but $\pi_2$ no longer has the property a).

We proceed in the same fashion. For $n$ even, we construct $\pi_{n+1}$ by adding
new lines, and for $n$ odd, we construct $\pi_{n+1}$ by adding new points.

Let $\Pi = \bigcup_{n=0}^\infty \pi_n,$ and define a line in $\Pi$ to be a subset 
$L \subset  \Pi$ such that
for all large enough $n,$ $L\cap \pi_n$ is a line of $\pi_n.$
\end{hartshorne}\<close>

text \<open>\begin{hartshorne}
\prop[2.2] 
If $\pi_0$ contains at least four points, no three of which lie on a line, then $\Pi$
 is a projective plane.

\proof 
Note that for $n$ even, $\pi_n$ satisfies b), and for $n$ odd $\pi_n$ satisfies a). Hence $\Pi$ 
satisfies both a) and b), i.e. it satisfies P1 and P2. If $P, Q, R$ are three non-collinear
 points of $\pi_0$,
 then they are also non-collinear in $\Pi.$ Thus P3 is also satsified. Axiom P4 is left to the
 reader: show each line of $\Pi$ has at least three points.
\endproof

\defn[Confined configuration]. A \term{confined configuration} is 
a configuration in which each point is on at least three
lines, and each line contains at least three points.

Example. The configuration of Desargues’ Theorem is confined. 

\prop[2.3] Any finite,
 confined configuration of $\Pi$ is already contained
in $\pi_0.$

\proof For a point $P in \Pi$ we define its \term{level} as the smallest $n \ge 0$ such 
that $P \in \pi_n.$
For a line $L \subset \Pi,$ we define its \term{level} to be the smallest $n \ge 0$ such 
that $L\cap \pi_n$ is a line.

Now let $\Sigma$ be a finite confined configuration in $\Pi,$ and let $n$ be the maximum level
of a point or line in $\Sigma.$ Suppose it is a line $l \subset  \Sigma$ which has level $n.$
 (A similar argument holds if a point has maximum level.) Then $l \cap \pi_n$ is a line, 
and  $l \cap \pi_{n-1}$ 
is not a line. If $n=0,$ we are done,
$\Sigma\ subset \pi_0.$ Suppose $n>0.$
Then $l$ occurs as the line joining two points
 of $\pi_{n-1}$ which did not lie on a line. But all points of 
$\Sigma$ have level $\le n,$ so they 
are in $\pi_n,$ so $l$ can contain at most two of them, which is a contradiction.
\endproof

Example (A non-Desarguesian projective plane). Let $\pi_0$ be four points and no lines. 
Let $\Pi$ be the free projective plane generated by $\pi_0.$ Note, as a Corollary of the previous
proposition, that $\Pi$ is infinite, and so every line contains infinitely many points. Thus 
it is possible to choose $O,A,B,C,$ no three collinear, $A'$ on $OA,$ $B'$ on $OB,$ $C'$ on $OC,$ such 
that they form 7 distinct points and $A', B', C'$ are not collinear. Then construct
\begin{align*}
P &= AB \cdot A'B'\\
Q &= AC \cdot A'C'\\ 
R &= BC \cdot B'C'.
\end{align*}

Check that all $10$ points are distinct. If Desargues’ Theorem is true in $\Pi,$ then $P,Q,R$ 
lie on a 
line, hence these $10$ points and $10$ lines form a confined configuration, which 
must lie in $\pi_0,$ and that's a contradiction, 
 since $\pi_0$ has only four points.
\end{hartshorne}\<close>

locale free_projective_plane_data =
    fixes meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool"
begin
datatype fpoint = A | B | C | D | Intersect nat fline fline and
fline = Join nat fpoint fpoint

text \<open>Now we want to build a pair, consisting of a point set PS and a line set LS, and define 
functions called ``Plevel'' and ``Llevel'' that returns the level of any point or line. The level for 
$A,B,C,D $ is zero; for other points and lines, it's the ``nat'' that's part of the constructor
data.

Then we want to assert that \textbf{if} several things are true, namely
\begin{itemize}
\item if $U \in PS$ and $Plevel(U) = 0$, then $U = A,B,C,$ or $D$.  
\item if $k \in LS$ then $Llevel(k) > 0$.  
\item $Join (n P Q) \in LS$ implies that $P,Q \in PS, level(P) < n, level(Q) < n$.
\item $Intersect (n k m) \in PS$ implies that $k,m \in LS, level(k) < n, level(m) < n$.
\end{itemize}
and a couple more that say that whenever two points aren't already on a line, their ``Join'' is in 
the line-set, and the dual of this, \textbf{then} $LS$ and $PS$ cannot contain a Desargues configuration 
because it'd have to be at level zero, which only contains four points. 

Presumably we need some lemmas first, like "if P = Intersect (n k m) and level(l) < n, then NOT meets 
P l" (i.e., k and m are the only lines of level less than n that intersect P). 

Oops! Slight revision: should an element of LS be a SET of points? That seems to be Hartshorne's 
definition, and it's a legal line if its intersection with level n is a line at level n, for all sufficiently large n.

  \<close>
(* Need to make some assumptions about flines and fpoints, then prove configs lie in pi0. *)

end
end

