theory Chapter4
  imports Chapter1 Chapter2 Complex_Main


begin
declare [[smt_timeout = 200]]
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

 

lemma dmeets_p1aa_1:
  assumes "P\<noteq>Q"
  shows "\<exists>l. dmeets P l \<and> dmeets Q l"
  unfolding dmeets_def
  using assms p2 by blast

lemma dmeets_p1aa: "P \<noteq> Q \<longrightarrow> (\<exists>l. dmeets P l \<and> dmeets Q l)"

  using dmeets_p1aa_1 by auto

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
  using assms dmeets_def p2 by blast


lemma "dmeets_p1b": "P \<noteq> Q \<longrightarrow> (\<exists>!l. dmeets P l \<and> dmeets Q l)"
  using dmeets_p1aa dunique_lines by blast 

lemma "dmeets_p2": "\<forall>l m. l \<noteq> m \<longrightarrow> (\<exists>!P. dmeets P l \<and> dmeets P m)"

  by (simp add: dmeets_def p1)

lemma "dmeets_p3": "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> projective_plane_data.collinear dmeets P Q R"
proof - 
  obtain l m n where lmn: "l \<noteq> m \<and> l \<noteq> n \<and> m \<noteq> n \<and> \<not> projective_plane_data.collinear meets l m n"
    using p3 by blast 
  obtain P where P: "dmeets P l \<and> dmeets P m" using dmeets_p2 lmn by blast 
  obtain Q where Q: "dmeets Q m \<and> dmeets Q n" using dmeets_p2 lmn by blast 
  obtain R where R: "dmeets R n \<and> dmeets R l" using dmeets_p2 lmn by blast 
  have PQ: "P \<noteq> Q" using P Q collinear_def dmeets_def lmn by blast 
  have PR: "P \<noteq> R" using P R collinear_def dmeets_def lmn by blast 
  have RQ: "R \<noteq> Q" using R Q collinear_def dmeets_def lmn by blast
  thus ?thesis by (smt P Q R dunique_lines lmn projective_plane_data.collinear_def) qed 

lemma "pmeets_p4": "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> dmeets P l \<and> dmeets Q l \<and> dmeets R l"
proof - 
  obtain A where A:"\<not> meets l A" using dmeets_def dmeets_p3
    by (smt projective_plane_data.collinear_def)
  obtain m n k where mnk:"meets m A \<and> meets n A \<and> meets k A \<and> m \<noteq> n \<and> n \<noteq> k \<and> m \<noteq>k"
    using p4 by blast
  obtain P where P: "meets l P \<and> meets m P"
    by (metis mnk p1)
 obtain Q where Q: "meets l Q \<and> meets n Q"
   by (metis mnk p1)
 obtain R where R: "meets l R \<and> meets k R"
   by (metis mnk p1)
 have "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> meets l P \<and> meets l Q \<and> meets l R"
   by (metis A P Q R mnk p2)
  thus ?thesis unfolding dmeets_def by auto
qed

lemma "extra_line":
  fixes P
  shows "\<exists> k . \<not> meets P k"
  using dmeets_def dmeets_p3 projective_plane_data.collinear_def by force

text\<open>\daniel This allows us an easy way to prove the duals of theorems
in a projective plane\<close>

interpretation dual:projective_plane dmeets
  unfolding projective_plane_def
  using dmeets_p1b dmeets_p2 dmeets_p3 local.pmeets_p4 by blast

lemma linesOffPoints: (* dual of pointOffLines *)
  fixes P::"'point" and Q::"'point"
  assumes "P \<noteq> Q"
  shows "\<exists>l::'line. (\<not> meets P l) \<and> (\<not> meets Q l)"
  using dual.pointOffLines assms dmeets_def by blast

text\<open>\done\<close>
end


end
text\<open>\seiji \caleb\<close>
locale desarguian_projective_plane_plus = 
    projective_plane_plus meets +
    desarguian_proj_plane meets 
    for meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool"
begin
lemma perspective_implies_concurrent:
  fixes a and b and c and a' and b' and c' and p
  assumes "desarguian_plane_data.perspective_from_point local.dmeets p a b c a' b' c'"
  shows "(projective_plane_data.concurrent meets a a' p)"
proof -
  obtain P where P: "local.dmeets p P \<and> local.dmeets a P"
    by (metis (full_types) dmeets_def dmeets_p1aa p4)
  obtain A where A: "local.dmeets a A \<and> local.dmeets a' A"
    by (metis (full_types) dmeets_def dmeets_p1aa p4)
  obtain P' where P': "local.dmeets p P' \<and> local.dmeets a' P'"
    by (metis (full_types) dmeets_def dmeets_p1aa p4)

qed
lemma dual_desargues: 
  fixes a and b and c and a' and b' and c' and p
  assumes "desarguian_plane_data.perspective_from_point local.dmeets p a b c a' b' c'"
  shows "desarguian_plane_data.perspective_from_line local.dmeets a b c a' b' c'"
proof -
  have conc1: "(projective_plane_data.concurrent meets a a' p)" try
    by (smt assms concurrent_def desarguian_plane_data.intro desarguian_plane_data.perspective_from_point_def dmeets_def dmeets_p1b dmeets_p2 dmeets_p3 local.pmeets_p4 projective_plane.intro projective_plane_data.collinear_def)

qed
end

text\<open>\done \done\<close>