theory HoareLogicTR 

imports Main "HOL-Hoare.Hoare_Logic"

begin

section \<open>Hoare Logic in Isabelle/HOL\<close>

 

lemma imp_pot:
"VARS (a::int) (b::nat) (p::int) (i::nat)
{a=A \<and> b=B}
i := 0; p := 1;
WHILE i<b
  INV { p = a^i \<and> i\<le> b \<and> a=A \<and> b = B}
  DO p := p * a;i:=i+1 OD
{p = A^B}"
apply (vcg)
apply (auto)
done

lemma imp_pot_isar:"VARS (a::int) (b::nat) p i
{a=A \<and> b=B}
i := 0; p := 1;
WHILE i<b
  INV { p = a^i \<and> i\<le> b \<and> a=A \<and> b = B}
  DO p := p * a;i:=i+1 OD
{p = A^B}"
proof (vcg)
  fix a b p i 
  let ?INV = "p = a ^ i \<and> i \<le> b \<and> a = A \<and> b = B"
  assume ass:"?INV  \<and> i < b"
  show "p * a = a ^ (i + 1) \<and> i + 1 \<le> b \<and> a = A \<and> b = B"
    proof - 
      from ass obtain 1: "p = a ^ i" and 2:"i \<le> b"
      and 3:"a = A \<and> b = B" and 5:"i<b"  by blast
      from 1 have 6:"p*a=a^i*a" by simp
      from this have 7:"p * a = a ^ (i + 1)" by simp
      from 5 have 8:"i+1\<le>b" by simp
      from this 3 7 8 show ?thesis by simp
    qed 
qed (auto)

section \<open>Preliminary Example - List Reversal\<close>

lemma hd_tl:"xs \<noteq> [] \<Longrightarrow> xs = hd xs # tl xs"
  by simp 


fun tail_rev::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
"tail_rev [] acc = acc" |
"tail_rev (x#xs) acc = tail_rev xs (x # acc)"

lemma tail_rev:"\<forall>ys. tail_rev xs ys = rev xs @ ys"
apply (induction xs)
apply (auto)
done

lemma "tail_rev xs [] = rev xs" by (simp add:tail_rev)


lemma hd_tl_app:"xs \<noteq> [] \<Longrightarrow> xs = [hd xs] @ tl xs"
  by simp
 
lemma impRev: "VARS (acc::'a list) (xs::'a list)
 {xs=X}
 acc:=[];
 WHILE xs \<noteq> []
 INV {rev(xs)@acc = rev(X)}
 DO acc := (hd xs # acc); xs := tl xs OD
 {acc=rev(X)}"
apply (vcg) 
apply (simp)
using hd_tl_app apply (force)
apply (auto)
done

lemma impRev_isar: "VARS acc x
 {x=X}  acc:=[];
 WHILE x \<noteq> []  INV {rev(x)@acc = rev(X)}
 DO acc := (hd x # acc); x := tl x OD
 {acc=rev(X)}"
proof (vcg)
  fix acc x
  assume ass:"rev x @ acc = rev X \<and> x \<noteq> []"
  show "rev (tl x) @ hd x # acc = rev X"
    proof - 
      from ass obtain 1:"rev x @ acc = rev X" 
        and 2:" x\<noteq>[]" by blast
      from 2 have "x = hd x # tl x"  by simp
      from 1 and this  have 3:"rev x = rev (hd x # tl x)" by simp
      have "rev (hd x # tl x) = rev (tl x) @ [hd x]" by simp
      from 3 and this have "rev x =  rev (tl x) @ [hd x]" by simp
      from this and 1 show ?thesis by simp
    qed 
qed (auto)


section \<open>Case Study: Insertion Sort\<close> 

fun ins::"'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "ins x [] = [x]" |
  "ins x (y # ys) = 
      (if x \<le> y then (x # y # ys) else y#ins x ys)" 

fun iSort::"('a::linorder) list \<Rightarrow> 'a list" where 
"iSort [] = []" | 
"iSort (x # xs) = ins x (iSort xs)"

fun le::"('a::linorder) \<Rightarrow> 'a list \<Rightarrow> bool"  where 
"le x [] = True" | 
"le x (y # ys) = (x \<le>y \<and> le x ys)"

fun isorted::"('a::linorder) list \<Rightarrow> bool" where   
"isorted [] = True" | 
"isorted (x # xs) = (le x xs \<and> isorted xs)"

fun count:: "'a \<Rightarrow> 'a list \<Rightarrow> int" where 
"count x [] = 0" |
"count x (y # ys) =(if x=y then  1 + count x ys else count x ys)"

fun tail_iSort::"('a::linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"tail_iSort [] acc = acc" |  
"tail_iSort (x#xs)  acc = tail_iSort xs (ins x acc)"

value "iSort [12,-3,-4,200,2::int]"
value "tail_iSort [12,-3,-4,200,2::int] []"
value "isorted(tail_iSort [12,-3,-4,200,2::int] [1,2,3])"

text \<open>
lemma le_ins: "le x (ins a xs) = (x \<le> a \<and> le x xs)"                       sorry
lemma le_mon:"x\<le>y \<Longrightarrow> le y xs \<Longrightarrow> le x xs"                                sorry
lemma ins_sorted: "isorted (ins a xs) = isorted xs"                        sorry
lemma is_sorted:"isorted(iSort xs)"                                        sorry
lemma ins_count:
 "count x (ins k xs) = (if x = k then 1 + count x xs else count x xs)"   sorry
lemma count_sum:"count x (xs @ ys) = count x xs + count x ys"              sorry
lemma len_sort:"length(iSort xs) = length xs"                              sorry
lemma count_iSort: "count x (iSort xs) = count x xs"                       sorry
lemma ins_len:"length (ins k xs) = 1 + length xs"                          sorry
\<close>

lemma le_ins: "le x (ins a xs) = (x \<le> a \<and> le x xs)"
  apply (induction xs)
  apply auto
done

lemma le_mon:"x\<le>y \<Longrightarrow> le y xs \<Longrightarrow> le x xs" 
  apply (induction xs)
  apply (auto)
done 

lemma ins_sorted: "isorted (ins a xs) = isorted xs"
  apply (induct_tac xs)
  apply (auto simp add: le_ins le_mon)
done

lemma is_sorted:"isorted(iSort xs)" 
  apply (induction xs)
  apply (auto simp add:ins_sorted)
done  

lemma ins_count:
   "count x (ins k xs) = (if x = k then 1 + count x xs 
                          else count x xs)" 
apply (induction xs)
apply (auto)
done 


lemma count_sum:"count x (xs @ ys) = count x xs + count x ys" 
      (is "?P xs")
proof (induction xs)
  show "?P []" by simp 
next 
  fix a xs 
  assume IH: "count x (xs @ ys) = count x xs + count x ys"
  show "count x ((a # xs) @ ys) = count x (a # xs) +  count x ys"
    proof (cases "x=a")
      assume h0:"x=a" 
      have "count x ((a # xs) @ ys) = count x (a # (xs @ ys))" 
          by simp
      also have "\<dots> = 1 + count x (xs @ ys)" using h0 by simp
      also have "\<dots> = (1 + count x xs)  + count x ys" 
          using IH h0 by simp
      also have "\<dots> =  count x (a # xs) + count x ys" using h0 by simp
      finally show ?thesis by this
    next
      assume h1:"x\<noteq>a" 
      have "count x ((a # xs) @ ys) = count x (a # (xs @ ys))" 
          by simp
      also have "\<dots> =  count x (xs @ ys)" using h1 by simp
      also have "\<dots> = count x xs  + count x ys" 
          using IH h1 by simp
      also have "\<dots> =  count x (a # xs) + count x ys" using h1 by simp
      finally show ?thesis by this
    qed
qed

lemma ins_len:"length (ins k xs) = 1 + length xs" 
apply (induction xs)
apply (auto)
done 

lemma len_sort:"length(iSort xs) = length xs" 
apply (induction xs)
apply (simp_all add:ins_len)
done 

lemma count_iSort: "count x (iSort xs) = count x xs" 
apply (induction xs)
apply (auto simp add: ins_count)
  done 

 
definition is_perm::"'a list \<Rightarrow> 'a list \<Rightarrow> bool" 
where "is_perm l1 l2 \<equiv> length l1 = length l2 
                        \<and> (\<forall>x. count x l1 = count x l2)"

lemma inss_hoare: "VARS xs ys :: ('a::linorder) list
 {xs=X}
 ys:=[];
 WHILE xs \<noteq> []
    INV {isorted ys \<and> is_perm X (ys @ xs)}
 DO ys := ins (hd xs) ys; xs := tl xs OD
{isorted ys \<and> is_perm X ys}"
apply (vcg)  
apply (auto simp add:is_perm_def) \<comment> \<open> 1 \<close>
   apply (simp add: ins_sorted)  \<comment> \<open> 2 \<close>
   apply (simp add: ins_len) \<comment> \<open> 3 \<close>
   apply (smt count.simps(2) count_sum hd_Cons_tl ins_count) \<comment> \<open> 4 \<close>
done

lemma inss_isar_draft:
"VARS xs ys :: ('a::linorder) list
       {xs=X}
       ys:=[];
       WHILE xs \<noteq> []
       INV {isorted ys \<and> is_perm X (ys @ xs)}
       DO ys := ins (hd xs) ys; xs := tl xs OD
       {isorted ys \<and> is_perm X ys}"
proof (vcg)
   fix xs ys 
   assume ass:"(isorted ys \<and> is_perm X (ys @ xs)) \<and> xs \<noteq> []"   
   show "isorted (ins (hd xs) ys) \<and> is_perm X ((ins (hd xs) ys) @ tl xs)" 
    proof (rule conjI)
       show "isorted (ins (hd xs) ys)" sorry
    next
       have pg1:"length X  =  length ((ins (hd xs) ys) @ tl xs)" sorry 
       have pg2:"\<forall> k. count k X = count k (ins (hd xs) ys @ tl xs)" sorry
       from pg1 pg2 show "is_perm X (ins (hd xs) ys @ tl xs)" sorry 
   qed
qed (auto simp add:is_perm_def)


lemma inss_isar: "VARS xs ys :: ('a::linorder) list
       {xs=X}
       ys:=[];
       WHILE xs \<noteq> []
       INV {isorted ys \<and> is_perm X (ys @ xs)}
       DO ys := ins (hd xs) ys; xs := tl xs OD
       {isorted ys \<and> is_perm X ys}"
proof (vcg)
   fix xs ys 
   assume ass:"(isorted ys \<and> is_perm X (ys @ xs)) \<and> xs \<noteq> []"   
   show "isorted (ins (hd xs) ys) \<and> is_perm X ((ins (hd xs) ys) @ tl xs)" 
      proof (rule conjI)
         from ass have "isorted ys" by simp
         from this show "isorted (ins (hd xs) ys)" by (simp add:ins_sorted)
      next 
        from ass have 1:"is_perm X (ys @ xs)" and 2:"xs \<noteq> []" by auto 
        from 2 have hdtl:"xs = hd xs # tl xs" by simp 
        from 1 have 3:"\<forall> x. count x X = count x (ys @ xs)" by (simp add:is_perm_def)
        have pg1:"length X  =  length ((ins (hd xs) ys) @ tl xs)"
           proof - 
               from 1 have 4:"length X = length (xs @ ys)" by (simp add:is_perm_def)
               also have "\<dots>= length xs + length ys" by simp
               also have "\<dots> =  1 + length ys + length xs - 1" by simp
               also have "\<dots> = length (ins (hd xs) ys) + length (tl xs)"
                                by (simp add: "2" ins_len)
               also have "\<dots> = length ((ins (hd xs) ys) @ tl xs)" by simp
               finally show ?thesis  by simp
           qed 
        have pg2:"\<forall> k. count k X = count k (ins (hd xs) ys @ tl xs)" 
           proof (rule allI)
             fix k
             have "count k X = count k ((ins (hd xs) ys) @ tl xs)"
                proof (cases "k= hd xs")
                   assume case1: "k = hd xs" 
                   have "count k ((ins (hd xs) ys) @ tl xs) = 
                         count k (ins (hd xs) ys) + count k (tl xs)"  
                             by (simp add:count_sum)
                   also have "\<dots> = 1 + count k ys + count k (tl xs)" 
                       by (simp add:case1 ins_count)
                   also have "\<dots> =  count k ys + 1 + count k (tl xs)" by simp
                   also have "\<dots>= count k ys + count k ((hd xs) # tl xs)" 
                        by (simp add: case1) 
                   also have "\<dots>= count k ys + count k xs"  using hdtl by auto 
                   also have "\<dots>= count k (ys @ xs)" by (simp add:count_sum)
                   also have "\<dots>= count k X" by (simp add: "3")
                   finally show "count k X = count k ((ins (hd xs) ys) @ tl xs)"
                      by simp
                next 
                   assume case2: "k \<noteq> hd xs" 
                    have "count k ((ins (hd xs) ys) @ tl xs) = 
                         count k (ins (hd xs) ys) + count k (tl xs)"  
                             by (simp add:count_sum)
                   also have "\<dots> = count k ys + count k (tl xs)" 
                       by (simp add:case2 ins_count)
                   also have "\<dots>= count k ys + count k ((hd xs) # tl xs)" 
                        by (simp add: case2) 
                   also have "\<dots>= count k ys + count k xs"  using hdtl by auto 
                   also have "\<dots>= count k (ys @ xs)" by (simp add:count_sum)
                   also have "\<dots>= count k X" by (simp add: "3")
                   finally show "count k X = count k ((ins (hd xs) ys) @ tl xs)"
                      by simp
                qed
                from this show "count k X = count k (ins (hd xs) ys @ tl xs)"
                  by assumption
             qed
        from pg1 pg2 show "is_perm X (ins (hd xs) ys @ tl xs)" 
             by (simp add:is_perm_def)
      qed
qed (auto simp add:is_perm_def)

end