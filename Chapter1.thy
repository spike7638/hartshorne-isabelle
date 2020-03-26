(* Things left to do in Chapter 1:
  ** Prove that the completion of an affine plane is a projective plane. 
  ** do the "problems" from the back of the book about the cardinality of lines in 
     an affine plane, or a projective plane, etc. --- basically the first five or six
     problems from the back of the book. 
*)

chapter \<open>Introduction: Affine Planes and Projective Planes\<close>
text \<open>
\begin{hartshorne}
Projective geometry is concerned with properties of incidence --- properties which are 
invariant under stretching, translation, or rotation of the plane. Thus in the axiomatic 
development of the theory, the notions of distance and angle will play no part.
However, one of the most important examples of the theory is the real projective plane,
and there we will use all the techniques available (e.g. those of Euclidean geometry and analytic 
geometry) to see what is true and what is not true.
\end{hartshorne}\<close>

section \<open>Affine geometry\<close>
text\<open>
\begin{hartshorne}
Let us start with some of the most elementary facts of ordinary plane geometry, which we will
take as axioms for our synthetic development.

Definition. An \emph{affine plane} is a set, whose elements are called points, and a set of
subsets, called \emph{lines}, satisfying the following three axioms, A1–A3. We will use the
terminology ``$P$ lies on $l$'' or ``$l$ passes through $P$'' to mean the point $P$ is an 
element of the line $l.$
\begin{itemize}
\item{A1.}
 Given two distinct points $P$ and $Q$, there is one and only one line containing both $P$ and $Q.$
We say that two lines are parallel if they are equal or if they have no points in common.\\
\item{A2.}
Given a line $l$ and a point $P$ not on $l,$ there is one and only one line 
$m$ which is parallel to $l$ and which passes through $P.$\\

\item{A3.} There exist three non-collinear points. (A set of points $P_1, \ldots, P_n$ is said to be 
\emph{collinear} if there exists a line $l$ containing them all.)
\end{itemize}

Notation: 
\begin{align}
P \ne Q && \text{$P$ is not equal to $Q$.} \\
P \in l && \text{$P$ lies on $l$.}\\
l \cap m && \text{the intersection of $l$ and $m$.}\\
l \parallel m && \text{$l$ is parallel to  $m$.}\\
\forall && \text{for all.}\\
\exists && \text{there exists.}\\
\implies && \text{implies.}
\iff && \text{if and only if.}
\end{align}
\end{hartshorne}
\<close>
text \<open>
\spike
To translate to Isabelle, we are saying that to have an affine plane, you need two types (which are
how we choose to represent
sets in Isabelle), and a relationship between them. The statement "meets P l" indicates the notion
that the "point" P lies on the "line" l. For Hartshorne, we would say P is an element of l, but using
point sets as lines turns out to be a horrible idea in Isabelle, so we just deal with `meets.' 
\<close>
text \<open>
We've based our theory on "Complex\_Main" instead of main so that we have the datatype "real". To 
characterize affine and projective planes (the main topics of study) we use ``locales'', an Isabelle 
construct that lets us say ``this entity satisfies this collection of defining axioms.'' The declaration
about ``smt\_timeout'' lets one of the solvers we use have extra time in which to 
discover or confirm correctness of proofs. \done
\<close>
theory Chapter1
  imports Complex_Main

begin
declare [[smt_timeout = 200]]

locale affine_plane_data =
    fixes meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool"

begin
    definition parallel:: "'line  \<Rightarrow> 'line \<Rightarrow> bool" (infix "||" 50)
      where "l || m \<longleftrightarrow> (l = m \<or> \<not> (\<exists> P. meets P l  \<and> meets P m))"
 
    definition collinear :: "'point  \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> bool"
      where "collinear A B C \<longleftrightarrow> (\<exists> l. meets A l \<and> meets B l \<and> meets C l)"
  end
  value "affine_plane_data"

  locale affine_plane =
    affine_plane_data meets
  for meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool" +
  assumes
    a1: "P \<noteq> Q \<Longrightarrow> \<exists>!l. meets P l \<and> meets Q l" and
    a2: "\<not> meets P l \<Longrightarrow> \<exists>!m. l || m \<and> meets P m" and
    a3: "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R"

begin

text \<open>
\begin{hartshorne}
Example. The ordinary plane, known to us from Euclidean geometry, satisfies the axioms A1–A3, and 
therefore is an affine plane. [NB: We'll return to this below. -- jfh]

A convenient way of representing this plane is by introducing Cartesian coordinates, 
as in analytic geometry. Thus a point $P$ is represented as a pair $(x, y)$ of real numbers. 
(We write $x, y \in \Bbb R$.)

[Omitted picture]
\prop[1.1] Parallelism is an equivalence relation.

\end{hartshorne}
\<close>

  text \<open>
\begin{hartshorne}
\defn[equivalence relation] A relation $\sim$ is an equivalence relation if it has the following
three properties:
\begin{enumerate}
\item Reflexive: $a \sim a$
\item Symmetric: $a \sim b \implies b \sim a$
\item Transitive: $a \sim b$ and $b \sim c \implies a \sim c$.
\end{enumerate}

\proof (of proposition)
We must check the three properties:
1. Any line is parallel to itself, by definition. 

2. $l \parallel m \implies m \parallel l$ by definition.

3. If $l \parallel m$, and $m \parallel n$, we wish to prove $l \parallel n.$

If $l=n$ ,there is nothing to prove.If $l \ne n$,and there is a point
$P \in l \cap n$,then $l, n$ are both $\parallel m$ and pass through $P$, which is impossible by 
axiom A2. We conclude that $l \cap n = \emptyset$ (the empty set), and so $l \parallel n.$
\end{hartshorne}
\<close>

text \<open>
\spike
We now move on to prove some of the elementary claims in the text above, albeit slightly out of 
order. 
\done\<close>

  lemma symmetric_parallel: "l || m \<Longrightarrow> m || l"
    using parallel_def by auto

text \<open>
\spike
Here's the original proof of that theorem; apparently practice makes perfect (or at least it
shortens things a good deal:
\begin{lstlisting}[language=Isabelle]{}
proof -
    fix l :: "'line" and m :: "'line"
    assume one_direction: "l || m"
    show "m || l"
    proof -
      have "(l = m \<or> \<not> (\<exists> P. meets P l  \<and> meets P m))" 
        using one_direction parallel_def by auto
      from this have "(m = l \<or> \<not> (\<exists> P. meets P m  \<and> meets P l))"
        by auto
      thus "m || l"
        by (simp add: parallel_def)
    qed
  qed
\end{lstlisting}
\done\<close>


  lemma reflexive_parallel: "l || l"
    using parallel_def by blast
(*
  proof - 
    have "l = l" 
      by auto
    thus "l || l"
      using parallel_def by auto
  qed
*)
  lemma transitive_parallel: "\<lbrakk>l || m ;  m || n\<rbrakk> \<Longrightarrow> l || n"
    by (metis a2 parallel_def)
(*
  proof - 
    fix l :: "'line" and m :: "'line" and n :: "'line"
    assume lm: "l || m"
    assume mn: "m || n"
    show "l || n"
    proof -
      have "(l = m \<or> \<not> (\<exists> P. meets P l  \<and> meets P m))"
        using lm parallel_def by blast
      have "(m = n \<or> \<not> (\<exists> P. meets P m  \<and> meets P n))" 
        using mn parallel_def by blast
      thus "l || n"
        by (metis a2 lm parallel_def)
    qed
  qed
*)
  text \<open>\daniel\haoze Equivalence relations can be proved using the following structure with
exported rules.\<close>
lemma equivp_parallel: "equivp parallel"
proof (rule equivpI)
  show "reflp parallel"
    by (simp add: reflexive_parallel reflpI)
  show "symp parallel"
    by (simp add: symmetric_parallel sympI)
  show "transp parallel"
    by (simp add: transitive_parallel transpI)
qed
  text \<open>\done\<close>
end

text  \<open>\spike To help Isabelle along, we insert a tiny theorem giving a different 
characterization of parallelism. \done\<close>

theorem (in affine_plane_data) parallel_alt:
  fixes l
  fixes m
  assumes "l \<noteq> m"
  assumes "\<forall>P. (\<not>meets P l) \<or> (\<not> meets P m)"
  shows "l || m"
proof -
  have "\<not> (\<exists> P. meets P l \<and> meets P m)"
    using assms(2) by auto
  thus "l || m" 
      using assms(2) parallel_def by auto
qed

text  \<open>\begin{hartshorne}
\prop[1.2] Two distinct lines have at most one point in common.

\proof For if $l, m$ both pass through two distinct points $P, Q,$ then by axiom A1, $l = m.$ \endproof

Example. An affine plane has at least four points. There is an affine plane with four points.

Indeed, by A3 there are three non-collinear points. Call them $P, Q, R.$ By A2 there is a line 
$l$ through $P,$ parallel to the line $QR$ joining $Q$ and $R,$ which exists by A1. 
Similarly, there is a line $m \parallel  PQ$, passing through $R.$

Now $l$ is not parallel to $m$ ($l \nparallel m$). For if it were, then we would have 
$PQ \parallel m \parallel l \parallel QR$
and hence $PQ \parallel QR$ by Proposition 1.1. This is impossible, however, because $P Q \ne QR$, 
and both contain $Q.$

Hence $l$ must meet $m$ in some point $S.$ Since $S$ lies on $m,$ which is parallel to $PQ$, and 
different from $PQ,$ $S$ does not lie on $PQ,$ so $S\ne P$,and $S \ne Q$ .Similarly $S \ne R$. Thus
$S$ is indeed a fourth point. This proves the first assertion.

Now consider the lines $PR$ and $QS$. It
may happen that they meet (for example in the real projective plane they will (proof?)). 
On the other hand, it is consistent with the axioms to assume that they do not meet.
In that case we have an affine plane consisting of four points $P, Q, R, S$ and six lines 
$PQ, PR, PS, QR, QS, RS,$ and one can verify easily that the axioms A1–A3 are satisfied. 
This is the smallest affine plane. [NB: We'll return to this final claim presently.]

\end{hartshorne}
\<close>

  (* Two lines meet in at most one point *)
  lemma (in affine_plane) prop1P2: "\<lbrakk>l \<noteq> m; meets P l; meets P m; meets Q l; meets Q m\<rbrakk> \<Longrightarrow> P = Q"
    using a1 by auto


text \<open>\daniel
We can also prove some basic theorems about affine planes not in Hartshorne. The first is that every
point lies on some line; the second is that every line contains at least one point. \done\<close>
  (* Examples of some easy theorems about affine planes, not mentioned in Hartshorne *)
  (* Every point lies on some line *)
  lemma (in affine_plane) containing_line: "\<forall>S. \<exists>l. meets S l"
    using a2 by blast

  (* Every line contains at least one point *)
  lemma (in affine_plane) contained_point: "\<forall>l. \<exists>S. meets S l"
    using a1 a2 a3 parallel_def collinear_def by metis


  text \<open>\daniel We enlarge on these to show that every line contains at least \emph{two} points;
we could also show (but don't) that every point lies on at least two lines.\<close>

lemma (in affine_plane) contained_points: "\<forall> l.  \<exists> S T.  S\<noteq>T \<and> meets S l \<and> meets T l"
  proof -
    fix l::"'line"
    obtain S where S:"meets S l" using contained_point
      by auto
    obtain P Q R where PQR: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R"
      using a3 by blast
    obtain A B where AB: "A \<noteq> B \<and> A \<noteq> S \<and> B \<noteq> S \<and> \<not> collinear A B S"
      by (smt PQR collinear_def prop1P2)
    obtain C where C: "(C=A \<or> C=B) \<and> \<not> meets C l"
      using AB S collinear_def by blast
    obtain m where m: "meets C m \<and> meets S m"
      by (metis AB a1)
    obtain D where D: "(D = A \<or> D = B) \<and> D \<noteq> C"
      using AB by blast
    thus ?thesis
      by (smt AB C D S a2 affine_plane_data.collinear_def m parallel_def symmetric_parallel transitive_parallel)
  qed

  text \<open>\done\<close>

  section  \<open> The real affine plane\<close>
  text \<open> Hartshorne mentioned, just after the definition of an affine plane and some notational 
notes, that the ordinary affine plane is an example of an affine plane. We should prove 
that it's actually an affine plane. It's pretty clear how to represent points --- pairs of real 
numbers --- but what about lines? A line is the set of points satisfying an equation of 
the form Ax + By + C = 0, with not both of A and B being zero. The problem is that there's 
no datatype for ``pair of real numbers, at least one of which is nonzero''. We'll have 
to hack this by breaking lines into ``ordinary'' and ``vertical'', alas.   \<close>

  datatype a2pt = A2Point "real" "real"

  datatype a2ln = A2Ordinary "real" "real" 
                | A2Vertical "real"
  text "Ordinary m b represents the line y = mx+b; Vertical xo is the line x = xo. With this in 
mind, we define the  `meets' operation for this purported plane, using cases for the definition."

  fun a2meets :: "a2pt \<Rightarrow> a2ln \<Rightarrow> bool" where
    "a2meets (A2Point x y) (A2Ordinary m b) = (y = m*x + b)" |
    "a2meets (A2Point x y) (A2Vertical xi) = (x = xi)"

  definition a2parallel:: "a2ln  \<Rightarrow> a2ln \<Rightarrow> bool" (infix "a2||" 50)
      where "l a2|| m \<longleftrightarrow> (l = m \<or>  (\<forall> P. (\<not> a2meets P l)  \<or> (\<not>a2meets P m)))"
  text\<open> Notice that I've written the definition of parallel for the euclidean affine plane
as a forall rather than exists. I think this might make things easier.\<close>
  text\<open>Now we'll write some small lemmas, basically establishing the three axioms.\<close>
  text\<open> I'm going to venture into a new style of writing theorems and proofs, one that's
particularly applicable when you're showing something exists by constructing it. Here is 
an example in the case of real numbers: if $r < s$, then there's a real number strictly between
them. We could write this as ``$r < s$ shows that there is a $t$ . ($(r < t)$ and $(t < s)$)'' (although it turns out we'd have
to start with ``\texttt{(r::real) < s ...}'' to tell Isar not to assume that r is a natural number -- after all, 
this is one of those cases where type-inference has no idea whether ``$<$'' means less-than on the reals,
or the integers, or the natural numbers, or ...)

Anyhow, in this new style, we would type the theorem like this:

\begin{lstlisting}[language=Isabelle]{}
theorem mid:
  fixes r :: real
  assumes lt : "r < s"
  shows "\<exists>t. r < t \<and> t < s"
proof
  let ?t = "(r + s) / 2"
  from lt show "r < ?t \<and> ?t < s" by simp
qed
\end{lstlisting}
\<close>

  text\<open>The nice thing about this style is that it takes care of "fix"ing things in the theorem statement,
and takes care of assuming the antecedent (which we always end up doing in the proof anyhow), and
then makes clear what we're going to actually show. We will treat this as a pattern henceforth.

A note about naming: Everything related to real-affine-2-space will be written with a prefix
``A2''. When we want to state axiom 3 for A2, we'll write ``A2\_a3''. Sometimes we'll need some preliminary
results, and we'll append an ``a'' or ``b'' or ``c'', etc., before stating the main result. \caleb \<close>

theorem A2_a1a: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q"
  shows "\<exists> ls . a2meets P ls \<and> a2meets Q ls"
proof (cases P, cases Q)
  fix x0 y0 assume P: "P = (A2Point x0 y0)"
  fix x1 y1 assume Q: "Q = (A2Point x1 y1)" 
  show ?thesis
  proof (cases "(x0 = x1)")

    case True (* Case where x0 = x1 *)
    let ?ll = "A2Vertical x0"
    have m1:  "a2meets P ?ll" using P by simp
    have m2:  "a2meets Q ?ll" using Q True by simp
    have "a2meets P ?ll \<and> a2meets Q ?ll" using m1 m2 by auto
    thus ?thesis by auto
  
  next
    case False (* Case where x0 \<noteq> x1*) 
    let ?rise = "y1 - y0"
    let ?run  = "x1 - x0"
    let ?m    = "?rise/?run"
    let ?b    = "y0 - ?m*x0"
    let ?ll   = "A2Ordinary ?m ?b"

    have m3: "a2meets P ?ll" using P by simp
    have m4: "a2meets Q ?ll"
    proof -
      have s0: "y1*?run/?run = ?m*x1 + (y0 * ?run/?run - ?m*x0)"
        by argo
      have s1: "y1 = ?m*x1 + ?b" using s0 False by auto
      thus ?thesis using s1 Q a2meets.simps(1) by blast

    qed
    show ?thesis using m3 m4 by blast
  qed
qed


text\<open>\done For this next theorem, it might make sense to phrase it as "P notequal Q lets us derive a unique
line l such that..."
but that would require proving the existence of l (which we just did in the previous lemma) and
then proving that it's unique. Instead, we can just say that if l and m both contain the 
distinct points P and Q, then l must equal m. From this, and the previous lemma, we can then 
conclude that axiom 1 is true (which we'll do in a final theorem). 

This is arguably the ugliest theorem in the bunch, because it involves four cases (one each for 
l and m being ordinary or vertical). Once again, we start by providing names for the constructor
arguments for P and Q:
 \seiji\<close>

lemma A2_a1b: 
  fixes P :: a2pt
  fixes Q
  fixes l
  fixes m
  assumes pq: "P \<noteq> Q"
  assumes pl : "a2meets P l"
  assumes ql : "a2meets Q l"
  assumes pm : "a2meets P m"
  assumes qm : "a2meets Q m"
  shows "l = m"

proof (cases P, cases Q)
    fix x0 y0 assume P: "P = (A2Point x0 y0)"
    fix x1 y1 assume Q: "Q = (A2Point x1 y1)" 
    show ?thesis
    proof (cases "(x0 = x1)")
      case True
      then show ?thesis 
        by (smt P Q a2ln.inject(1) a2meets.elims(2) a2meets.simps(2) pl pm pq ql qm)
    next
      case False
      then show ?thesis
        by (smt P Q a2ln.inject(1) a2meets.elims(2) a2meets.simps(2) a2pt.inject crossproduct_noteq pl pm ql qm)
    qed
  qed


lemma A2_a1:
  fixes P :: a2pt
  fixes Q
  assumes pq: "P \<noteq> Q"
  shows "\<exists>! ls . a2meets P ls \<and> a2meets Q ls"
proof -
  show ?thesis using pq A2_a1a A2_a1b by auto
qed

text \<open>\done Whew! We've proved axiom 1 for the real affine plane. On to Axiom 2. This one's 
a little trickier because we're proving a conjunction. \caleb\<close>
lemma A2_a2a (*existence*):
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> a2meets P l"
  shows  "\<exists>k. a2meets P k \<and> l a2|| k"

proof (cases P)
  fix x0 y0 assume P: "P = (A2Point x0 y0)"
  have existence: "\<exists>m. l a2|| m \<and> a2meets P m"
  proof (cases l)
    case (A2Vertical x1)
    obtain m where mvert: "m = (A2Vertical x0)" 
      by simp
    have lparallelm: "a2parallel l m"
      by (metis A2Vertical a2meets.simps(2) a2parallel_def a2pt.exhaust mvert)
    have Ponm: "a2meets P m"
      by (simp add: P mvert)
    then show ?thesis
      using lparallelm by auto
  next
    case (A2Ordinary slope intercept)
    obtain intercept2 where a: "intercept2 = y0 - slope * x0" 
      by simp
    obtain line2 where eq: "line2 = (A2Ordinary slope intercept2)" 
      by simp
    have PonLine2: "a2meets P line2"
      by (simp add: P a eq)
    then show ?thesis
      by (smt A2Ordinary a2meets.elims(2) a2meets.simps(1) a2parallel_def eq) 
  qed
  thus ?thesis
    by auto 
qed

text \<open> \spike At this point, I went down a rabbit hole searching for proofs of the other half

of axiom 2, and kept getting into trouble when dealing with the (pretty simple) algebra 
of straight lines. So I backed off and proved a bunch of small lemmas, partly as practice 
at proving things, and partly to give Isabelle a helping hand when it came to more complicated
things. So here are proofs of things like "a vertical and ordinary line cannot be parallel; if two 
ordinary lines have different slopes, then they intersect; if two vertical lines intersect, they're 
the same; if two ordinary lines with the same slope intersect, then they're the same; if two
ordinary lines are parallel and intersect, then they're the same. \done \<close>

text\<open> Let's start with something dead simple: the other form of parallelism: if 
there's no P meeting both l and m, then they're parallel. \caleb\<close>

lemma A2_parallel_0: 
  fixes l
  fixes m
  fixes P
  assumes nomeet: "\<not> (\<exists>P . a2meets P l \<and> a2meets P m)"
  shows "l a2|| m"

  using a2parallel_def nomeet by auto


text \<open>\done a vertical and ordinary line cannot be parallel \caleb \<close>
lemma A2_basics_1: 
  fixes l
  fixes m
  assumes lo: "l = A2Vertical x"
  assumes mo: "m = A2Ordinary s b "
  shows lm_noparr : "\<not> (l a2|| m)"
proof -

  obtain P where P: "P = (A2Point x (x * s + b)) \<and> a2meets P m"
    using mo by force
  have "a2meets P l"
    by (simp add: P lo)
  thus ?thesis
    using P a2parallel_def lo mo by blast

qed

text \<open>\done if two ordinary lines have different slopes, then they intersect \caleb \<close>
lemma A2_basics_2: 
  fixes l
  fixes m
  assumes lo: "l = A2Ordinary s1 b1"
  assumes mo: "m = A2Ordinary s2 b2"
  assumes sdiff: "s1 \<noteq> s2"
  shows lm_noparr2 : "\<not> (l a2|| m)"
proof - 
  obtain x where x: "x = (b2 - b1) / (s1 - s2)"
    by simp
  obtain y where y: "y = s1 * x + b1"
    by simp
  obtain P where P: "P = (A2Point x y)"
    by simp
  have pl: "a2meets P l"
    by (simp add: P lo y)
  have eq1: "s1 * x + b1 = s1 * (b2 - b1) / (s1 - s2) + b1" by (simp add: x)
  have eq2: "s1 * (b2 - b1) / (s1 - s2) + b1 = (b2 * s1 - b1 * s1) / (s1 - s2) + b1"
    by argo
  have eq3: "(b2 * s1 - b1 * s1) / (s1 - s2) + b1 = (b2 * s1 - b1 * s1) / (s1 - s2) + (s1 * b1 - s2 * b1) / (s1 - s2)" 
    by (simp add: mult_diff_mult sdiff)
  have eq4: "(b2 * s1 - b1 * s1) / (s1 - s2) + (s1 * b1 - s2 * b1) / (s1 - s2) =  (s1 * b2 - b1 * s2) / (s1 - s2)" 
    by argo
  have eq5: "s2 * x + b2 = s2 * (b2 - b1) / (s1 - s2) + b2" by (simp add: x)
  have eq6: "s2 * (b2 - b1) / (s1 - s2) + b2 = (b2 * s2 - b1 * s2) / (s1 - s2) + b2"
    by argo
  have eq7: "(b2 * s2 - b1 * s2) / (s1 - s2) + b2 = (b2 * s2 - b1 * s2) / (s1 - s2) + (s1 * b2 - s2 * b2) / (s1 - s2)" 
    by (simp add: mult_diff_mult sdiff)
  have eq8: "(b2 * s2 - b1 * s2) / (s1 - s2) + (s1 * b2 - s2 * b2) / (s1 - s2) =  (s1 * b2 - b1 * s2) / (s1 - s2)"
    by argo
  have eq9: "y = s2 * x + b2"
    by (simp add: eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 y)
  have pm: "a2meets P m" 
    by (simp add: P mo eq9)
  thus ?thesis
    using a2parallel_def lo mo pl sdiff by auto   
qed

text\<open>\done Trying to prove axiom 2 directly seems near impossible. Let's start with 
something simpler: if l and m are parallel, and l is vertical, so is m (and similarly
for ordinary) \caleb\<close>

lemma A2_parallel_1: 
  fixes l
  fixes m
  assumes lo: "l = A2Vertical x2 "
  assumes lm_parr : "l a2|| m"
  shows "\<exists>s2. m = A2Vertical s2 "

  by (metis A2_basics_1 a2ln.exhaust lm_parr lo)
    


text\<open> Let's do the other half of that: if l is ordinary, and m is parallel, then m is ordinary \<close>
lemma A2_parallel_2: 
  fixes l
  fixes m
  assumes lo: "l = A2Ordinary s1 b1 "
  assumes lm_parr : "l a2|| m"
  shows "\<exists>s2 b2. m = A2Ordinary s2 b2 "
  by (metis A2_basics_1 a2ln.exhaust a2parallel_def lm_parr lo)
  

text\<open> And a third half: if l and m are parallel and ordinary, them their slopes are the same \<close>
lemma A2_parallel_3: 
  fixes l
  fixes m
  assumes lo: "l = A2Ordinary s1 b1 "
  assumes mo: "m = A2Ordinary s2 b2 "
  assumes lm: "l a2|| m"

  shows "s1 = s2"
  using A2_basics_2 lm lo mo by blast 
 

text\<open>\done  Recall that axiom 2 states that there's a unique m 
through P, parallel to l.    
We'll phrase that just the way we did A1.a1b: \caleb \seiji\<close>
(* a2: "\<not> meets P l \<Longrightarrow> \<exists>!m. l || m \<and> meets P m" *)

lemma A2_a2b: 
  fixes P
  fixes l
  fixes m
  fixes k
  assumes pl : "\<not> a2meets P l"
  assumes pm : "a2meets P m"
  assumes pk : "a2meets P k"
  assumes lm_parr : "l a2|| m"
  assumes lk_parr : "l a2|| k"
  shows "m = k"
proof (cases m)
  case (A2Ordinary x11 x12)
  obtain xl yl where l_ord: "l = (A2Ordinary xl yl)"
    by (metis A2Ordinary A2_basics_1 a2meets.elims(3) lm_parr pl)
  obtain xk yk where k_ord: "k = (A2Ordinary xk yk)"
    using A2_parallel_2 l_ord lk_parr by blast
  have equality: "xl = xk \<and> x11 = xl"
    using A2Ordinary A2_basics_2 k_ord l_ord lk_parr lm_parr by force 
  have m_par_k: "m a2|| k"
    using A2Ordinary a2meets.elims(2) a2parallel_def equality k_ord by force
  then show ?thesis
    using a2parallel_def pk pm by blast
next
  case (A2Vertical x2)
  obtain xl where l_vert: "l = (A2Vertical xl)"
    by (metis A2Vertical A2_parallel_2 a2ln.distinct(1) a2meets.elims(3) lm_parr pl)
  obtain xk where k_vert: "k = (A2Vertical xk)"
    using A2_parallel_1 l_vert lk_parr by blast
  have equal: "xk = x2"
    by (metis A2Vertical a2meets.elims(2) a2meets.simps(2) k_vert pk pm)
  then show ?thesis
    using A2Vertical k_vert by auto
qed
lemma A2_a2: 
  fixes P
  fixes l
  assumes "\<not> a2meets P l"
  shows "\<exists>! m. a2meets P m \<and> m a2|| l"
  by (smt A2_a2a A2_a2b a2parallel_def)



lemma A2_a3:
  shows  "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> (\<nexists> m. a2meets P m \<and> a2meets Q m \<and> a2meets R m)"
proof -
  obtain P where P: "P = (A2Point 0 0)" by simp
  obtain Q where Q: "Q = (A2Point 1 0)" by simp
  obtain R where R: "R = (A2Point 0 1)" by simp

  have "(\<nexists> m. a2meets P m \<and> a2meets Q m \<and> a2meets R m)"
    by (metis A2_a1b P Q R a2meets.simps(2) a2pt.inject zero_neq_one)

  thus ?thesis
    by (metis (full_types) A2_a1 A2_a2)

qed
text\<open>\done \done\<close>

lemma A2_a3x:
  shows "\<not> (\<exists> m. a2meets (A2Point 0 0)  m \<and> a2meets (A2Point 0 1) m \<and> a2meets (A2Point 1 0) m)"

  by (metis A2_a1b a2meets.simps(1) a2pt.inject add.right_neutral mult_zero_left zero_neq_one)
  

lemma A2_a3y: (* alternative formulation -- harder to read, easier to prove *)
  fixes m
  assumes "a2meets (A2Point 0 0) m"
  assumes "a2meets (A2Point 0 1) m"
  shows "\<not> (a2meets (A2Point 1 0) m)"
  using A2_a3x assms(1) assms(2) by blast

lemma A2_a3z1: (* alternative formulation -- harder to read, easier to prove *)
  fixes m
  assumes "a2meets (A2Point 0 0) m"
  assumes "a2meets (A2Point 0 1) m"
  shows "m = (A2Vertical 0)"
  by (smt a2ln.inject(1) a2meets.elims(2) a2pt.inject assms(1) assms(2))

text\<open> At this point we've established that the Cartesian Plane satisfies Cartesian 
versions of the three axioms, etc., but it'd be nice to be able to say that as
a *structure*, it matches the Isabelle "locale" that we defined. \caleb \seiji 
\<close>

theorem A2_affine: "affine_plane(a2meets)"
  unfolding affine_plane_def
  apply (intro conjI)
  subgoal using A2_a1a A2_a1b by auto
  subgoal
    by (smt A2_a2 a2parallel_def affine_plane_data.parallel_def)
  apply (simp add: affine_plane_data.collinear_def)
  using A2_a3 by auto


text\<open>\done \done  Examples of some easy theorems about affine planes, not mentioned in Hartshorne. \jackson \<close>      



(* Some HW Problems to give you practice with Isabelle:
Try to state and prove these:
1. Every line contains at least two points (this is stated for you below, but
with "sorry" as a "proof". 
2. Every line contains at least three points [false!]
*)

text\<open>To prove that every line contains at least two points, firstly we should think about where the
contradiction is when the line contains only one point. Usually, contradiction happens when something
violates a unique existence. For example, in A2, if an assumption leads to the conclusion that there
are more lines that could parallel to a specific line passing through the same point, then the assumption
is proved to be false. Here are the ideas for our proof.

i. If l only contains one point Q and point P != point Q, then every line passing through P is parallel
to l.
ii. To prove the contradiction to A2, we have to prove there are at least two lines passing through P. 
NB: need lemma contained-lines: for every point, there are at least two lines that pass through that point.
iii.Lemma contained-lines can be proved with the three non-collinear points P Q R in A3. Two cases:
1. The point is P or Q or R. 2. The point T is different from those 3 points. Then PT, QT, RT cannot
be the same line, which proves that at least two lines pass through T.

(I'm still Struggling with the grammar in Isabelle. I’ll try to finish these two lemmas soon and
 I’m also looking for help ;)
\siqi\<close>
lemma (in affine_plane) contained_lines: "\<forall> S. \<exists>l m. l\<noteq>m \<and> meets S l \<and> meets S m"
sorry 
(*
proof -
  obtain P Q R where PQR: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R"
    using a3 by auto
  fix S
  show ?thesis
  proof (cases "S \<noteq> P \<and> S \<noteq> Q \<and> S \<noteq> R")
    case True
    then obtain SP where SP: " meets S SP \<and> meets P SP"
      using a1 by blast
    obtain SR where SR: "meets S SR \<and> meets R SR" 
      using True a1 by blast
    obtain SQ where SQ: "meets S SQ \<and> meets Q SQ"
      using True a1 by blast
    have nosameline: "\<nexists>l. l=SP \<and> l=SQ \<and> l=SR" try
      using PQR SP SQ SR affine_plane_data.collinear_def by force
    have differtwolines: "SP \<noteq> SQ \<or> SP \<noteq> SR \<or> SQ \<noteq> SR"
      using nosameline by auto
    then show "\<exists>l,m \<in> {SP, SQ, SR}. l\<noteq>m \<and> meets S l \<and> meets S m"
    show ?thesis
      sorry
  next
    case False
    show ?thesis
  proof (cases "S = P")
    case True
    then obtain SQ1 where SQ1: "meets S SQ1 \<and> meets Q SQ1"
      by (metis PQR affine_plane.a1 affine_plane_axioms)
    obtain SR1 where SR1: "meets S SR1 \<and> meets R SR1"
      by (metis PQR a1)
    have nosameline1: "SQ1 \<noteq> SR1" 
      using PQR SQ1 SR1 True affine_plane_data.collinear_def by force
    have "SQ1 \<noteq> SR1 \<and> meets S SQ1 \<and> meets S SR1"try
      by (simp add: SQ1 SR1 nosameline1)
    show ?thesis
      sorry
    next 
      case False
      show ?thesis
      proof (cases "S = Q")
        case True
        then obtain SP2 where SP2: "meets S SP2 \<and> meets P SP2" 
          using False affine_plane.a1 affine_plane_axioms by fastforce
        obtain SR2 where SR2: "meets S SR2 \<and> meets R SR2"
          by (metis PQR a1)
        have nosameline2: "SP2 \<noteq> SR2"
          using PQR SP2 SR2 True affine_plane_data.collinear_def by force
        have "SP2 \<noteq> SR2 \<and> meets S SP2 \<and> meets S SR2"
          using SP2 SR2 nosameline2 by blast
        show ?thesis
          sorry
        case False
        then obtain SP3 where SP3: "meets S SP3 \<and> meets P SP3"
          using True by blast
        obtain SQ3 where SQ3: "meets S SQ3 \<and> meets Q SQ3"
          using False True by blast
        have nosameline3: "SP3 \<noteq> SQ3"
          using False True by auto
        have "SP3 \<noteq> SQ3 \<and> meets S SP3 \<and> meets S SQ3"
          using False True by auto
*)


  text \<open>
 We now try to prove that every affine plane contains at least four points. Sledgehammer 
(a generally-useful approach) doesn't get anywhere with this one. 

Here's Hartshorne's proof, though, so we can use the pieces to construct an Isabelle proof.

i. by A3 there are three distinct non-collinear points; call them P,Q,R. 
ii. By A1, there's a line, which I'll call QR, through Q and R. 
iii. By A2, there's a line l through P, parallel to QR.
iv. Similarly, there's a line PQ containing P and Q. 
v. There's a line m through R, parallel to the line PQ.

CASES: l is parallel to m, or it is not.  

vi. l is not parallel to m, for if it were, then PQ || m || l || QR, hence PQ || QR (by 
the lemmas about parallelism) and since both contain Q,  they are identical, but then P,Q,R are collinear,
which is a contradiction. 

vii. So l and m are nonparallel, and they share some point S. 

viii. S lies on m, which is parallel to PQ but not equal to it,
hence disjoint from it (see definition of parallel), so S is not on PQ.

ix.  Hence S != P, S != Q. 

x. Similar (arguing about l), we get  S != R. 

xi. Hence the four points P,Q,R,S are all distinct, and we are done. 
\caleb \seiji\<close>
proposition (in affine_plane) four_points_necessary: "\<exists>(P :: 'point) (Q :: 'point) (R :: 'point) (S :: 'point). 
      P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S"
    proof -
      obtain P Q R where PQR: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R"
        using a3 by blast
      obtain PQ where PQ: "meets P PQ \<and> meets Q PQ" 
        using a1 PQR by blast
      obtain l where l: "meets R l \<and> l || PQ"
        by (metis PQ PQR affine_plane.a2 affine_plane.symmetric_parallel affine_plane_axioms collinear_def)
      obtain QR where QR: "meets Q QR \<and> meets R QR" 
        using a1 PQR by blast
      obtain m where m: "meets P m \<and> m || QR"
        by (metis QR PQR affine_plane.a2 affine_plane.symmetric_parallel affine_plane_axioms collinear_def)
      obtain S where S: "meets S l \<and> meets S m"
        by (metis (no_types, lifting) PQ QR affine_plane.a2 affine_plane_axioms l m parallel_def)
      have "S \<noteq> P \<and> S \<noteq> Q \<and> S \<noteq> R"
        by (metis PQ PQR QR S affine_plane_data.collinear_def affine_plane_data.parallel_def l m)
      thus ?thesis
        using PQR by blast
    qed

    text\<open>\done \done\<close>
    text\<open>\spike 
We've now proved the first assertion in the Example after Prop 1.2; we must also show there
IS an affine plane with four points. We'll do this two ways: by explicit construction, and
by using the wonderful ``nitpick'' prover.

We start by defining two datatypes, each of which is just an enumerated type; there
are four points and six suggestively-named lines:
\done\<close>
datatype pts = Ppt | Qpt | Rpt | Spt
datatype lns = PQln | PRln | PSln | QRln | QSln | RSln
text\<open>\spike 
Note: the above datatypes are meant to indicate that ``pts'' consists of four constructors,
one for each of $P,Q,R$ and $S$, and that the line we'd call $PQ$ in math is here 
constructed with
$PQln$, and we'll define the point-to-line meeting function (i.e., "the point is on the line" so that 
$P$ and $Q$ are on $PQln$, but $R$ and $S$ are not, etc. 

For the "meets" definition, the syntax looks OCaml-like.

We start by saying which points \emph{are} on the various lines, and then follow with those that
are not.
\done\<close>
  fun plmeets :: "pts \<Rightarrow> lns \<Rightarrow> bool" where
    "plmeets Ppt PQln = True" |
    "plmeets Qpt PQln = True" |
    "plmeets Ppt PRln = True" |
    "plmeets Rpt PRln = True" |
    "plmeets Ppt PSln = True" |
    "plmeets Spt PSln = True" |
    "plmeets Qpt QRln = True" |
    "plmeets Rpt QRln = True" |
    "plmeets Qpt QSln = True" |
    "plmeets Spt QSln = True" |
    "plmeets Rpt RSln = True" |
    "plmeets Spt RSln = True" |

    "plmeets Rpt PQln = False" |
    "plmeets Spt PQln = False" |
    "plmeets Qpt PRln = False" |
    "plmeets Spt PRln = False" |
    "plmeets Qpt PSln = False" |
    "plmeets Rpt PSln = False" |
    "plmeets Ppt QRln = False" |
    "plmeets Spt QRln = False" |
    "plmeets Ppt QSln = False" |
    "plmeets Rpt QSln = False" |
    "plmeets Ppt RSln = False" |
    "plmeets Qpt RSln = False"

text\<open>\spike 
  Now we'll assert that "plmeets" has all the properties needed to be an affine plane.
\done\<close>
  lemma four_points_a1: "P \<noteq> Q \<Longrightarrow> \<exists>! l . plmeets P l \<and> plmeets Q l"
    by (smt plmeets.elims(2) plmeets.simps(1) plmeets.simps(10) plmeets.simps(11) plmeets.simps(12) plmeets.simps(13) plmeets.simps(14) plmeets.simps(17) plmeets.simps(18) plmeets.simps(19) plmeets.simps(2) plmeets.simps(20) plmeets.simps(22) plmeets.simps(23) plmeets.simps(3) plmeets.simps(4) plmeets.simps(5) plmeets.simps(6) plmeets.simps(7) plmeets.simps(8) plmeets.simps(9) pts.exhaust)

  lemma four_points_a2a (*existence*): "\<not> plmeets (P :: pts) (l :: lns) \<Longrightarrow> \<exists>m. ((l = m)\<or> \<not> (\<exists> T. plmeets T l  \<and> plmeets T m)) \<and> plmeets P m"
    by (smt lns.simps(27) lns.simps(5) lns.simps(7) plmeets.elims(2) plmeets.simps(1) plmeets.simps(10) plmeets.simps(11) plmeets.simps(12) plmeets.simps(15) plmeets.simps(16) plmeets.simps(17) plmeets.simps(18) plmeets.simps(2) plmeets.simps(22) plmeets.simps(3) plmeets.simps(4) plmeets.simps(5) plmeets.simps(6) plmeets.simps(7) plmeets.simps(8) plmeets.simps(9) pts.exhaust)

text\<open>\spike 
Exercise: change the first "\<or>" in the lemma above to "\<and>"; that makes the lemma no longer true.
Attempt to prove it with "try" and then make sense of what the output is saying. 
\done\<close>

  lemma four_points_a2b(*uniqueness*): 
    "\<lbrakk>\<not> plmeets (P :: pts) (l :: lns); plmeets P m;  \<not> (\<exists> T. plmeets T l  \<and> plmeets T m); 
      plmeets P n;  \<not> (\<exists> U. plmeets U l  \<and> plmeets U n)\<rbrakk> 
     \<Longrightarrow> m = n"
    by (smt plmeets.elims(3) plmeets.simps(1) plmeets.simps(11) plmeets.simps(2) plmeets.simps(3) plmeets.simps(4) plmeets.simps(5) plmeets.simps(7) plmeets.simps(8) plmeets.simps(9) pts.simps(11) pts.simps(5) pts.simps(9))

  lemma four_points_a3:  "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> (\<not> (\<exists> m. plmeets P m \<and> plmeets Q m \<and> plmeets R m))"
    using four_points_a1 plmeets.simps(1) plmeets.simps(13) plmeets.simps(2) by blast

proposition four_points_sufficient: "affine_plane plmeets"
    unfolding affine_plane_def
    apply (intro conjI)
    subgoal using four_points_a1 by simp
    subgoal using four_points_a2a four_points_a2b by  (smt affine_plane_data.parallel_def plmeets.simps(11) plmeets.simps(12) plmeets.simps(24))
    apply (simp add: affine_plane_data.collinear_def)
    using four_points_a3 apply (blast)
    done

text\<open>\spike 
There's another way to show the existence of a 4-point affine plane: you claim that they
must have at least $5$ points, and let ``nitpick'' show that you're wrong. I'm going to use some
fancy mumbo-jumbo to write this so I can avoid writing out all the pairwise non-equalities; 
this fanciness is due to Manuel Eberl.

\begin{lstlisting}[language=Isabelle]{}
begin
  fix meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool"
  assume "affine_plane meets"

  have "\<exists>A::'point set. finite A \<and> card A = 5"
    by nitpick
end
\end{lstlisting}

To actually see what that produces, you'll need to type the code above into Isabelle. 
The results are pretty nifty, though,  hunh? 
It's a pain to try to read the output, but the gist is pretty clear: 4 points,
6 lines, each consisting of two distinct points.
\done\<close>

text  \<open> 
\begin{hartshorne}
\defn{Pencil} A pencil of lines is either a) the set of all lines passing through some point 
$P$ , or b) the set of all lines parallel to some line $l.$ In the second case we speak of 
a ``pencil of parallel lines.''

\defn{One-to-one correspondence} A one-to-one correspondence between two sets $X$ and $Y$ is a 
mapping $T : X \to Y$ (i.e., a rule $T,$ which associates to each element $x$ of the set
$X$ an element $T(x)=y 
\in Y$ such that $x_1\ne x_2 \implies T(x_1) \ne T(x_2),$ and
$\forall y \in Y, \exists x \in X$ such that $T(x)=y.$
\end{hartshorne}
\<close>
  definition (in affine_plane_data) point_pencil :: "'point  \<Rightarrow> 'line set"
    where "point_pencil P = {l . meets P l}"

  definition (in affine_plane_data) line_pencil :: "'line  \<Rightarrow> 'line set"
    where "line_pencil l = {m .  l||m}"

text  \<open> 
\spike
  I've skipped the notion of 1-1 correspondence, because Isabelle already has a notion 
  of bijections: there's a function "bij" that consumes a function and produces a boolean.
\done
\<close>


text  \<open> 
\spike
Completion of an affine plane to a projective plane 

Small problem: we need a data type for the points of the projective plane, which consists of
     all points of the affine plane together with all ideal points (i.e., line pencils), and we 
     need another for the lines of the PP, which consists of all lines of the affine plane (extended 
     by their associated ideal point) and the line at infinity consisting of all ideal points. We'll
     return to this, but first we need axioms for a projective plane.

The main problem is that we really, really need quotient types; with luck, Haoze and Daniel will 
soon have worked these out for us so that we can proceed. 
\done
\<close>
  
text  \<open> 
\begin{hartshorne}
\section*{Ideal points and the projective plane}

We will now complete the affine plane by adding certain ``points at infinity'' and thus arrive at 
the notion of the projective plane.

Let $A$ be an affine plane. For each line $l \in A,$ we will denote by $[l]$ the pencil of lines 
parallel to $l,$ and we will call $[l]$ an ``ideal point,'' or ``point at infinity,'' in the 
direction of $l.$ We write $P^{*} = [l]$.

We define the completion $S$ of $A$ as follows. The points of $S$ are the points of $A,$ plus all 
the ideal points of $A.$ A line in $S$ is either

\begin{enumerate}
\item An ordinary line $l$ of $A,$ plus the ideal point $P^{*} = [l]$ of $l$, or 
\item the ``line at infinity,'' consisting of all the ideal points of $A.$
\end{enumerate}

We will see shortly that $S$ is a projective plane, in the sense of the following definition.

\defn[Projective Plane] A ``projective plane'' $S$ is a set, whose elements are called points, 
and a set of subsets, called lines, satisfying the following four axioms.
\begin{enumerate}
\item[P1] Two distinct points $P, Q$ of $S$ lie on one and only one line. 
\item[P2] Any two lines meet in at least one point.
\item[P3] There exist three non-collinear points.
\item[P4] Every line contains at least three points.
\end{enumerate}

\prop[1.3] The completion $S$ of an affine plane $A,$ as described above, is a projective plane.

\proof. We must verify the four axioms P1–P4 of the definition. 
       
P1. Let $P,Q  \in S$.
\begin{enumerate}
\item If $P,Q$  are ordinary points of $A,$ then $P$ and $Q$ lie on only one line of $A.$ They do not 
lie on the line at infinity of $S,$ hence they lie on only one line of $S.$

\item If $P$ is an ordinary point, and $Q = [l]$ is an ideal point, we can find by A2 a line $m$ 
such that $P \in m$ and $m \parallel l$,i.e. $m \in [l]$,so that $Q$  lies on the extension of $m$ 
to $S.$ This is clearly the only line of $S$ containing $P$ and $Q.$

\item If $P, Q$ are both ideal points, then they both lie on the line of $S$ containing them.
\end{enumerate}

P2. Let $l, m$ be lines. 
\begin{enumerate}
\item If they are both ordinary lines, and $l \nparallel m,$ then they meet
in a point of $A.$ If $l \parallel m,$ then the ideal point $P^{*} =[l]=[m]$ lies on both $l$ and
$ m$ in $S.$
\item If $l$ is an ordinary line, and $m$ is the line at infinity, then $P^{*} = [l]$ lies on 
both $l$ and $m.$
\end{enumerate}

P3. Follows immediately from A3. One must check only that if $P,Q,R$ are non-collinear in $A,$ then
 they are also non-collinear in $S.$ Indeed, the only new line is the line at infinity, 
which contains none of them.

P4. Indeed, by Problem 1, it follows that each line of $A$ contains at least two points. 
Hence, in $S$ it has also its point at infinity, so has at least three points. \endproof

Examples. 

\begin{enumerate}
\item By completing the real affine plane of Euclidean geometry, we obtain the real projective plane.
\item By completing the affine plane of $4$ points, we obtain a projective plane with $7$ points.
\item Another example of a projective plane can be constructed as follows: let $\Bbb R^3$ be 
ordinary Euclidean 3-space, and let $O$ be a point of $\Bbb R^3.$ Let $L$ be the set of lines 
through $O.$

We define a point of $L$ to be a line through $O$ in $\Bbb R^3.$ We define a line of $L$ to be 
the collection of lines through $O$ which all lie in some plane through $O.$
Then $L$ satisfies the axioms P1–P4 (left to the reader), and so it is a projective plane.
\end{enumerate}
\end{hartshorne}
\spike
We'll go ahead and formalize the notion of projective plane as we did earlier; we won't prove 
proposition 1.3 (in Isabelle) until we have a good tool for quotient types, but we'll proceed 
with the work on the 7-point plane, etc.
\done
\<close>
  locale projective_plane_data =
    fixes meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool"

  begin
    definition collinear :: "'point  \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> bool"
      where "collinear A B C \<longleftrightarrow> (\<exists> l. meets A l \<and> meets B l \<and> meets C l)"

    definition concurrent :: "'line  \<Rightarrow> 'line \<Rightarrow> 'line \<Rightarrow> bool"
      where "concurrent l m n \<longleftrightarrow> (\<exists> P. meets P l \<and> meets P m \<and> meets P n)"
 
    definition injective :: "('a  \<Rightarrow> 'b)  \<Rightarrow> bool"
      where "injective f  \<longleftrightarrow> ( \<forall> P Q.  (f(P) = f(Q)) \<longleftrightarrow> (P = Q))" 
  end                   
                        

  locale projective_plane =
    projective_plane_data meets
  for meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool" +
  assumes
    p1: "P \<noteq> Q \<Longrightarrow> \<exists>!l. meets P l \<and> meets Q l" and
    p2: "l \<noteq> m \<Longrightarrow> \<exists>!P. meets P l \<and> meets P m" and
    p3: "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R" and
    p4: "\<forall> l. \<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> meets P l \<and> meets Q l \<and> meets R l"

begin

(* right here is where many small theorems about projective planes should go, theorems like "any
two lines in a projective plane have the same cardinality", etc. -- Spike *)
text  \<open> 
\spike
Here we have a few small theorems about projective planes, some from the exercises in Hartshorne,
others that just arose during class. 
 \done
\<close>
lemma pointOffLines:
  fixes l and m
  assumes "l \<noteq> m"
  shows "\<exists>T. (\<not> meets T l) \<and> (\<not> meets T m)"
proof -
  obtain I where I: "meets I l \<and> meets I m" 
    using p2 assms by blast
  obtain P where P: "meets P l \<and> P \<noteq> I" 
    using assms p4 I by metis
  obtain Q where Q: "meets Q m \<and> Q \<noteq> I"
    using assms p4 I by metis
   obtain PQ where PQ: "meets P PQ \<and> meets Q PQ"
    using P Q p1 by metis
  obtain R where R: "meets R PQ \<and> P \<noteq> R \<and> Q \<noteq> R"
    using p4 by blast
  have not_on_l: "\<not> meets R l"
    by (metis (no_types, lifting) I P PQ Q R assms projective_plane_axioms projective_plane_def)
  have not_on_m: "\<not> meets R m"
    by (metis (no_types, lifting) I P PQ Q R assms projective_plane_axioms projective_plane_def)
  thus ?thesis
    using not_on_l by auto 
qed

end

  (* Pending: The "Ideal" constructor probably needs to take a pencil of lines, or a quotient type *)
  datatype ('point, 'line) projPoint = Ordinary 'point | Ideal 'line
  datatype ('point, 'line) projLine = OrdinaryL 'line | Infty 

  fun projectivize :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (('a, 'b) projPoint \<Rightarrow> ('a, 'b) projLine \<Rightarrow> bool)" where
      "projectivize meets (Ordinary P) (OrdinaryL l) = meets P l" 
    | "projectivize meets (Ideal l) (OrdinaryL m) = affine_plane_data.parallel meets l m"
    | "projectivize meets (Ordinary P) Infty = False"
    | "projectivize meets (Ideal l) Infty = True"

  datatype ppts = Ppt | Qpt | Rpt | Spt | PQinf | PRinf | PSinf
  datatype plns = PQln | PRln | PSln | QRln | QSln | RSln | LAI
  fun pmeets :: "ppts \<Rightarrow> plns \<Rightarrow> bool" where
    "pmeets Ppt PQln = True" |
    "pmeets Qpt PQln = True" |
    "pmeets PQinf PQln = True" |

    "pmeets Ppt PRln = True" |
    "pmeets Rpt PRln = True" |
    "pmeets PRinf PRln = True" |

    "pmeets Ppt PSln = True" |
    "pmeets Spt PSln = True" |
    "pmeets PSinf PSln = True" |

    "pmeets Qpt QRln = True" |
    "pmeets Rpt QRln = True" |
    "pmeets PSinf QRln = True" |

    "pmeets Qpt QSln = True" |
    "pmeets Spt QSln = True" |
    "pmeets PRinf QSln = True" |

    "pmeets Rpt RSln = True" |
    "pmeets Spt RSln = True" |
    "pmeets PQinf RSln = True" |

    "pmeets PQinf LAI = True" |
    "pmeets PRinf LAI = True" |
    "pmeets PSinf LAI = True" |


    "pmeets Rpt PQln = False" |
    "pmeets Spt PQln = False" |
    "pmeets PRinf PQln = False" |
    "pmeets PSinf PQln = False" |

    "pmeets Qpt PRln = False" |
    "pmeets Spt PRln = False" |
    "pmeets PQinf PRln = False" |
    "pmeets PSinf PRln = False" |

    "pmeets Qpt PSln = False" |
    "pmeets Rpt PSln = False" |
    "pmeets PQinf PSln = False" |
    "pmeets PRinf PSln = False" |

    "pmeets Ppt QRln = False" |
    "pmeets Spt QRln = False" |
    "pmeets PQinf QRln = False" |
    "pmeets PRinf QRln = False" |

    "pmeets Ppt QSln = False" |
    "pmeets Rpt QSln = False" |
    "pmeets PQinf QSln = False" |
    "pmeets PSinf QSln = False" |

    "pmeets Ppt RSln = False" |
    "pmeets Qpt RSln = False" |
    "pmeets PRinf RSln = False" |
    "pmeets PSinf RSln = False" |

    "pmeets Ppt LAI = False" |
    "pmeets Qpt LAI = False" |
    "pmeets Rpt LAI = False" |
    "pmeets Spt LAI = False" 

  text \<open>Show that pmeets satisfies the projective plane axioms: \jackson \<close>

(* all of these can be proved by maaaany cases ... *)
lemma "pmeets_p1": "\<forall>P Q. P \<noteq> Q \<longrightarrow> (\<exists>!l. pmeets P l \<and> pmeets Q l)"
  sorry
lemma "pmeets_p2": "\<forall>l m. l \<noteq> m \<longrightarrow> (\<exists>!P. pmeets P l \<and> pmeets P m)"
  sorry
lemma "pmeets_p3": "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> projective_plane_data.collinear pmeets P Q R"
  by (smt pmeets.simps(1) pmeets.simps(24) pmeets.simps(3) pmeets_p2 ppts.distinct(8) projective_plane_data.collinear_def)
lemma "pmeets_p4": "\<forall> l. \<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> pmeets P l \<and> pmeets Q l \<and> pmeets R l"
  sorry

theorem "projective_plane pmeets"
  unfolding projective_plane_def
  using pmeets_p1 pmeets_p2 pmeets_p3 pmeets_p4 by auto

text \<open>\done\<close>

(*
theorem projectivization_p1: "\<lbrakk>P \<noteq> Q; affine_plane meets; pm = projectivize meets\<rbrakk> \<Longrightarrow>  \<exists>l. pm P l \<and> pm Q l"
sorry 
*)

(*
[This theorem should probably move up to just below the axioms for a projective plane -- jfh]

attempt to state a theorem about the the relation between the number of points on a line and
the number of points in the projective plane - Homer
lemma line_points_to_plane_points: "\<lbrakk>affine_plane meets; pm = projectivize meets\<rbrakk> \<Longrightarrow> 
        \<forall> l . card({P . pm P l}) = n \<longrightarrow> card({Q . \<exists> k . pm Q k}) = (n-1)^2 + n"
  sorry
*)
end


