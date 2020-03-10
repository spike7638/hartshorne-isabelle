theory Chapter4
  imports Chapter1 Complex_Main


begin
text \<open>
\spike
Soon to be filled in with some Hartshorne text. 

Key idea for this on 3/10: 

If you have a projective plane, defined by meets: points -> lines,
then you can define a NEW set of points:

type_equivalence ppoints = lines

and a new set of lines:

type_equivalence llines = points

in which you swap the role of "point" and "line". We already saw something like this in our 
work on the real projective plane, where I suggested that we could use the type "point" (3-coordinate
homogeneous vector) to represent a line (the "line" defined by "points in the plane orthogonal to the
given "normal" vector). 

With these two "new" types we can define a new "meets" function:

  fun dmeets :: "ppoint \<Rightarrow> lline \<Rightarrow> bool" where
    "dmeets P k = meets k P"

i.e., the "newpoint P" (which is really a line p) meets the "newline l" (which is really a point L)
exactly if L lies on p in our original projective plane. This new function, dmeets, (together with its
domain and codomain) constitutes a projective plane, called the "dual" of the original plane. 

To prove this, we have to (as usual) show the three axioms are true. 

\done\<close>


  locale projective_plane_plus =
    projective_plane meets
  for meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool" 
begin
    definition dmeets 
      where "dmeets P l  \<longleftrightarrow> ( meets l P)" 
(* Goal: to prove the theorem that "dmeets is a projective plane" *)

lemma dmeets_p1aa: "P \<noteq> Q \<longrightarrow> (\<exists>l. dmeets P l \<and> dmeets Q l)"
  sorry
(* first exercise: 
1. what happens if you remove the "forall Q : at the start of that lemma? 
2. rewrite that lemma as p1a, in fix-assume-show format
3. PROVE the lemma (you may need to delete the lemma I've written above, or it'll 
be used as the "proof" of the rewritten lemma.
*)

lemma dunique_lines: 
  fixes B
  fixes l
  fixes m
  assumes diff:"P \<noteq> B"
  assumes "dmeets P l"
  assumes "dmeets B l"
  assumes "dmeets P m"
  assumes "dmeets B m"
  shows "l = m" 
    sorry

lemma "dmeets_p1b": "P \<noteq> Q \<longrightarrow> (\<exists>!l. dmeets P l \<and> dmeets Q l)"
  using dmeets_p1aa dunique_lines by blast 

lemma "dmeets_p2": "\<forall>l m. l \<noteq> m \<longrightarrow> (\<exists>!P. dmeets P l \<and> dmeets P m)"
  sorry
lemma "dmeets_p3": "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> projective_plane_data.collinear dmeets P Q R"
  sorry

lemma "pmeets_p4": "\<forall> l. \<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> dmeets P l \<and> dmeets Q l \<and> dmeets R l"
  sorry

theorem "projective_plane dmeets"
  sorry
end



