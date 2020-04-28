theory FreePlane2
  imports Chapter2 (* Jordan_Normal_Form.Matrix *)
(* Need to somehow import AFP first; see https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2018-February/msg00129.html*)

begin

locale free_projective_plane_data =
    fixes meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool"
begin
datatype basepoint = AA | BB | CC | DD

fun lt:: "basepoint \<Rightarrow> basepoint \<Rightarrow> bool" where
    "lt AA BB = True"
  | "lt AA CC = True"
  | "lt AA DD = True"
  | "lt BB CC = True"
  | "lt BB DD = True"
  | "lt CC DD = True"
  | "lt U V = False"

lemma "antisymp lt" 
  by (smt antisympI free_projective_plane_data.lt.elims(2) free_projective_plane_data.lt.simps(15) free_projective_plane_data.lt.simps(7))

lemma "transp lt"
  by (smt free_projective_plane_data.basepoint.exhaust lt.simps(2,3,5,10,12,13) transpI)

datatype fpoint = Basepoint nat basepoint | Intersect nat fline fline and
fline =  Join nat fpoint fpoint | Extend nat fline 

(* "less than" rules for points and lines. *)
fun plt:: "fpoint  \<Rightarrow> fpoint \<Rightarrow> bool" 
     and llt:: "fline \<Rightarrow> fline \<Rightarrow> bool" 
where
    "plt (Basepoint n P) (Basepoint k Q) = (lt P Q)"
  | "plt (Basepoint n P) (Intersect i l m) = True"
  | "plt (Intersect i l m) (Basepoint n P)  = False"
  | "plt (Intersect i l m) (Intersect j n p)  
        = ((i < j) \<or> 
           ((i = j) \<and> (llt l n)) \<or>
           ((i = j) \<and> (l = n) \<and> (llt m p)))" 
  | "llt (Join i P Q)(Join j R S) = ((i < j) \<or> 
                                     ((i = j) \<and> (plt P  R)) \<or>
                                     ((i = j) \<and> (P = R) \<and> (plt Q  S)))"
  | "llt (Join i P Q) (Extend j m) = (i \<le> j)"
  | "llt (Extend j m) (Join i P Q)  = (j < i)"
  | "llt (Extend i l) (Extend j m) = ((i < j) \<or>
                                       (i = j) \<and> (llt l m))" 



fun nmeets :: "nat  \<Rightarrow> fpoint  \<Rightarrow> fline \<Rightarrow> bool" where
    "nmeets s (Basepoint i X) (Join j (Intersect ii u v)  (Intersect jj y z))  = False" 
  | "nmeets s (Basepoint i X) (Join j (Basepoint u Y)  (Intersect jj y z))  = ((i = 0) \<and> (u = 0) \<and> (X = Y))" 
  | "nmeets s (Basepoint i X) (Join j (Intersect ii u v)(Basepoint x Y) )  = ((i = 0) \<and> (x = 0) \<and> (X = Y))" 
  | "nmeets s (Basepoint i X) (Join j (Basepoint u Z) (Basepoint v Y) )  = ((i = 0) \<and> ((u = 0) \<and> (X = Y)) \<or> 
                                                                                      ((v = 0) \<and> (X = Z)))" 
  | "nmeets s (Basepoint i X) (Extend j l)  = ((i = 0) \<and> ((nmeets (s-1) (Basepoint i X) l)))" 
  
  | "nmeets s (Intersect i k l) (Extend j m)  = ((i = j) \<and> ((k = m) \<or> (l = m)))" 
  | "nmeets s (Intersect i l m) (Join j P Q)  = ((i = j) \<and> 
                                                 ((P = (Intersect i l m)) \<or> (Q = (Intersect i l m))))"
  
fun is_config :: " 'point set  \<Rightarrow> 'line set  \<Rightarrow> ('point   \<Rightarrow> 'line  \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_config Points Lines mmeets = (\<forall> k l P Q. (k \<in> Lines) \<and> (l \<in> Lines) \<and> (k \<noteq> l) \<and> (mmeets P k) \<and> (mmeets P l) 
   \<and> mmeets Q k \<and> mmeets Q l \<longrightarrow> P = Q)"

datatype lline = LLine "fpoint set" (* limit line *)

fun Plevel:: "fpoint\<Rightarrow>nat" where
  "Plevel (Basepoint n x) = n " |
  "Plevel (Intersect n k l) = n"

fun Llevel:: "fline \<Rightarrow> nat" where
  "Llevel (Join n k l) = n" |
  "Llevel (Extend n l) = n"

fun newPoint :: "nat  \<Rightarrow> fpoint set\<Rightarrow> fline set \<Rightarrow> fpoint \<Rightarrow> bool" where
 "newPoint i pts lines X = (\<exists>k l . (k \<in> lines) \<and> (l \<in> lines) \<and>
                            (X = Intersect i k l) \<and> 
                            (llt k l) \<and> 
                            (\<forall> P \<in> pts . \<not>(nmeets i P l \<and> nmeets i P k)))"

fun newLine :: "nat  \<Rightarrow> fpoint set\<Rightarrow> fline set \<Rightarrow> fline \<Rightarrow> bool" where
 "newLine i pts lines k = (\<exists>P Q . (P \<in> pts) \<and> (Q \<in> pts) \<and>
                            (k = Join i P Q) \<and> 
                            (plt P Q) \<and> 
                            (\<forall> m \<in> lines . \<not>(nmeets (i-1) P m \<and> nmeets (i-1) Q m)))"

fun extendedLine :: "nat  \<Rightarrow> fpoint set\<Rightarrow> fline set \<Rightarrow> fline \<Rightarrow> bool" where
 "extendedLine i pts lines k = (\<exists>l . (l \<in> lines)  \<and>
                            (k = Extend i l))" 

fun Pi:: "nat  \<Rightarrow> fpoint set" 
     and Lambda:: "nat \<Rightarrow> fline set" 
where
  "Pi 0 = {Basepoint 0 AA, Basepoint 0 BB, Basepoint 0 CC, Basepoint 0 DD }"
  | "Pi (Suc n) = Pi(n) \<union> Collect (newPoint (Suc n) (Pi n) (Lambda n)) " 
  | "Lambda 0 = {}"
  | "Lambda (Suc n) = Collect (newLine (Suc n) (Pi n) (Lambda n)) \<union> Collect (extendedLine (Suc n) (Pi n) (Lambda n))"


fun extends:: "fline \<Rightarrow> fline \<Rightarrow> bool" where
 "extends (Join i P Q) (Extend j n)  = False"  |
 "extends (Join i P Q) (Join j R S)  = ( (i = j) \<and> (P = R) \<and> (Q = S))" |
 "extends (Extend i n) (Join j R S)  = ( ((Join j R S) \<in> Lambda(j)) \<and> ((Extend i n) \<in> Lambda(i)) \<and>
                                         (j < i) \<and> (extends n (Join j R S)))" |
 "extends (Extend i n) (Extend j m)  = ( ((Extend j m) \<in> Lambda(j)) \<and> ((Extend i n) \<in> Lambda(i)) \<and>
                                         (j < i) \<and> (extends n m))"

(* Assert p1a, and see how hard it is to prove *)
fun lies_on_extension::"fpoint \<Rightarrow> fline \<Rightarrow> bool" where
 "lies_on_extension P (Extend j n)  = False"  |
 "lies_on_extension (Basepoint i XX) (Join j R S)  = ( (i = 0) \<and> (j = 1) \<and> ((R = Basepoint 0 XX)\<or> (S = Basepoint 0 XX)))" |
 "lies_on_extension (Intersect  i k n) (Join j R S)  = ( ((Join j R S) \<in> Lambda(j)) \<and> ((Intersect i k n ) \<in> Pi(i))
                                          \<and> ((extends k (Join j R S))\<or> (extends n (Join j R S))))" 

fun line_points:: "fline \<Rightarrow> fpoint set" where
  "line_points (Join i P Q) = {P, Q}" | 
  "line_points (Extend i k) = line_points(k) \<union> {X . \<exists>l . (l \<in> Lambda(i-1) \<and>
                            (X = Intersect i k l) \<and> 
                            (llt k l) \<and> 
                            (\<forall> P \<in> Pi(i) . \<not>(nmeets i P l \<and> nmeets i P k)))} \<union> 
                                        {X . \<exists>l . (l \<in> Lambda(i-1) \<and>
                            (X = Intersect i l k) \<and> 
                            (llt l k) \<and> 
                            (\<forall> P \<in> Pi(i) . \<not>(nmeets i P l \<and> nmeets i P k)))}"

fun is_limit_point:: "fpoint  \<Rightarrow> bool" where
  "is_limit_point (Basepoint 0 X) = True" | 
  "is_limit_point (Intersect i p q) = ((Intersect i p q) \<in> Pi(i))" |
  "is_limit_point Z = False"
  

(* Need to make some assumptions about flines and fpoints, then prove configs lie in pi0. *)

definition PS where "PS = {X. is_limit_point(X)}"

(* A limit line is a subset whose intersection with Pi(i) and onwards is always a line in Lambda(i),
i.e., it's the extension of some Join line Let's write it that way. *)

fun lsp:: "fline \<Rightarrow> fpoint \<Rightarrow> bool" where
  "lsp k P = lies_on_extension P k" 

fun UU :: "fline \<Rightarrow> fpoint set" where
  "UU k = {P . lsp k P  }"

definition LS where 
  "LS = {Z . \<exists>k i P Q . ((Z = UU k) \<and> (k = Join i P Q) \<and> (k \<in> Lambda i))}"

(*
definition LS where 
  "LS = {U . \<exists>(i::nat). \<forall> (j::nat) . 
     ((j < i) \<or> 
      (\<exists> (k::fline) . (k \<in> Lambda(j) \<and> (line_points(k) = U \<inter> Pi(j)))))}"
*)

fun fmeets:: "fpoint  \<Rightarrow> fpoint set  \<Rightarrow> bool" where
 "fmeets P k = (P \<in> k)"

lemma basepoints_in_PS:
  fixes P and X
  assumes "P \<in> PS" 
  assumes "P = Basepoint i X" 
  shows "(i = 0) \<and> (X= AA) \<or> (X=BB) \<or> (X=CC) \<or> (X= DD)"
proof -
  have i0: "i = 0" 
  proof (rule ccontr)
    assume "i \<noteq> 0"
    have "P \<in>PS" using assms(1) by auto 
    have A:"is_limit_point P" using PS_def assms(1) by blast
    have notA: "\<not>(is_limit_point P)" 
      using \<open>i \<noteq> 0\<close> assms(2) free_projective_plane_data.is_limit_point.elims(2) by auto
    thus False using A notA by auto
  qed
  have "P = Basepoint 0 X" by (simp add: \<open>i = 0\<close> assms(2))
  have "(X= AA) \<or> (X=BB) \<or> (X=CC) \<or> (X= DD)"
    using free_projective_plane_data.basepoint.exhaust by blast
  thus ?thesis using i0 by blast
qed

lemma fpp_a1a: 
  fixes P and Q
  assumes "P \<in> PS"
  assumes "Q \<in> PS"
  assumes "P \<noteq> Q"  
  shows "\<exists>l \<in> LS . fmeets P l \<and> fmeets Q l" 
proof -
  show ?thesis 
  proof (cases P)
    case (Basepoint i X)
    have "(i = 0) \<and> (X= AA) \<or> (X=BB) \<or> (X=CC) \<or> (X= DD)" using basepoints_in_PS Basepoint assms(1) by auto
    have Pform: "P = Basepoint 0 X"
      using Basepoint PS_def assms(1) free_projective_plane_data.is_limit_point.elims(2) by auto 
    show ?thesis
      proof (cases Q)
        case (Basepoint j Y)
        have "(j = 0) \<and> (Y= AA) \<or> (Y=BB) \<or> (Y=CC) \<or> (Y= DD)" using basepoints_in_PS Basepoint assms(2) by auto
        have Qform: "Q = Basepoint 0 Y"
          using Basepoint PS_def assms(2) free_projective_plane_data.is_limit_point.elims(2) by auto 
        then show ?thesis 
        proof -
          have "X \<noteq> Y" using assms(3) Pform Qform by simp
          show ?thesis 
          proof (cases "plt P Q")
            case True
            let ?k = "Join 1 P Q"
            let ?S = "UU ?k"
            have "fmeets P ?S" using fmeets.simps(1) UU.simps lsp.simps  by (simp add: Pform)  
            have "fmeets Q ?S" using fmeets.simps(1) UU.simps lsp.simps  by (simp add: Qform)
  (*          have "Lambda 0 = {}" try 
   "Lambda (Suc n) = Collect (newLine (Suc n) (Pi n) (Lambda n)) \<union> Collect (extendedLine (Suc n) (Pi n) (Lambda n))"
*)
            have L1a: "Lambda (1) = Collect (newLine (1) (Pi 0) (Lambda 0)) \<union> Collect (extendedLine (1) (Pi 0) (Lambda 0))" by simp
            have L1b: "Lambda (1) = Collect (newLine (1) (Pi 0) {}) \<union> Collect (extendedLine (1) (Pi 0) {})" by simp
            have p2emptyA: "\<forall> X . \<not> (extendedLine (1) (Pi 0) {} X)" by simp
            have p2emptyB: "Collect (extendedLine (1) (Pi 0) {}) = {}" using p2emptyA by simp
            have L1c: "Lambda (1) = Collect (newLine (1) (Pi 0) {}) \<union> {}" using L1b p2emptyB by blast
            have L1d: "Lambda (1) = Collect (newLine (1) (Pi 0) {})" using L1c by blast
            have k_in_Lam1: "newLine 1 (Pi 0) {} (Join 1 P Q)" unfolding newLine.simps 
              using Pform Qform True assms(1) assms(2) basepoints_in_PS by auto 
            have k_in_Lam1B: "?k \<in> Lambda 1" using k_in_Lam1 by simp
            have "?S \<in> LS" using LS_def
            proof -
              have zl1: "(Join 1 P Q) \<in> Lambda 1" using k_in_Lam1B by auto
              let ?Z = "UU ?k"
              have big: "?Z = UU ?k \<and> ?k = Join 1 P Q \<and> ?k \<in> Lambda 1" using zl1 by simp
              thus ?thesis using big LS_def by force
            qed
            have c1: "fmeets P  (UU (Join 1 P Q))" 
              using \<open>fmeets P (UU (Join 1 P Q))\<close> by blast
            have c2: "fmeets Q  (UU (Join 1 P Q))" 
              using \<open>fmeets Q (UU (Join 1 P Q))\<close> by blast
            have "(fmeets P  (UU (Join 1 P Q))) \<and> (fmeets Q  (UU (Join 1 P Q)))" using c1 c2 by auto 
            thus ?thesis 
              using \<open>UU (Join 1 P Q) \<in> LS\<close> by blast
          next
            case False
            have ineq: "plt Q P" 
              by (smt Basepoint False Pform \<open>X \<noteq> Y\<close> basepoint.simps(3) 
                    basepoint.simps(5) basepoint.simps(9) free_projective_plane_data.plt.simps(1) lt.elims(3))
            show ?thesis 
            proof-
            let ?k = "Join 1 Q P"
            let ?S = "UU ?k"
            have "fmeets P ?S" using fmeets.simps(1) UU.simps lsp.simps  by (simp add: Pform)  
            have "fmeets Q ?S" using fmeets.simps(1) UU.simps lsp.simps  by (simp add: Qform)
            have L1a: "Lambda (1) = Collect (newLine (1) (Pi 0) (Lambda 0)) \<union> Collect (extendedLine (1) (Pi 0) (Lambda 0))" by simp
            have L1b: "Lambda (1) = Collect (newLine (1) (Pi 0) {}) \<union> Collect (extendedLine (1) (Pi 0) {})" by simp
            have p2emptyA: "\<forall> X . \<not> (extendedLine (1) (Pi 0) {} X)" by simp
            have p2emptyB: "Collect (extendedLine (1) (Pi 0) {}) = {}" using p2emptyA by simp
            have L1c: "Lambda (1) = Collect (newLine (1) (Pi 0) {}) \<union> {}" using L1b p2emptyB by blast
            have L1d: "Lambda (1) = Collect (newLine (1) (Pi 0) {})" using L1c by blast
            have qp0: "Q \<in> Pi 0" 
              using Qform assms(2) basepoints_in_PS by auto
            have pp0: "P \<in> Pi 0" 
              using Pform assms(1) basepoints_in_PS by auto
            have k_in_Lam1: "newLine 1 (Pi 0) {} (Join 1 Q P)" unfolding newLine.simps using qp0 pp0 ineq try by simp
            have k_in_Lam1B: "?k \<in> Lambda 1" using k_in_Lam1 by simp
            have "?S \<in> LS" using LS_def
            proof -
              have zl1: "(Join 1 Q P) \<in> Lambda 1" using k_in_Lam1B by auto
              let ?Z = "UU ?k"
              have big: "?Z = UU ?k \<and> ?k = Join 1 Q P \<and> ?k \<in> Lambda 1" using zl1 by simp
              thus ?thesis using big LS_def by force
            qed
            thus ?thesis
              using \<open>fmeets P (UU (Join 1 Q P))\<close> \<open>fmeets Q (UU (Join 1 Q P))\<close> by blast
          qed
        qed
      qed
    next
      case (Intersect j m n)
        then show ?thesis sorry
      qed
  next
    case (Intersect i k l)
    then show ?thesis 
    proof (cases Q)
      case (Basepoint j A)
      then show ?thesis sorry
    next
      case (Intersect j m n)
      then show ?thesis sorry
    qed
  qed

theorem "projective_plane PS LS fmeets"
  sorry
end

