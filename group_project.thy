theory group_project
  imports HOL.HOL
begin

named_theorems ac_simps "associativity and commutativity simplification rules"
  and algebra_simps "algebra simplification rules for rings"

section \<open>Our Addition\<close>
locale magma =
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>\<^bold>*\<close> 70)

locale semigroup = magma +
  assumes assoc [simp]: "a \<^bold>* b \<^bold>* c = a \<^bold>* (b \<^bold>* c)"

section \<open>From Library\<close>
locale abel_semigroup = semigroup +
  assumes commute: "a \<^bold>* b = b \<^bold>* a"
  begin
    
    lemma left_commute [simp]: "b \<^bold>* (a \<^bold>* c) = a \<^bold>* (b \<^bold>* c)"
    proof -
      have "(b \<^bold>* a) \<^bold>* c = (a \<^bold>* b) \<^bold>* c"
        by (simp only: commute)
      then show ?thesis
        by (simp only: assoc)
    qed
end

locale monoid = semigroup +
  fixes z :: 'a (\<open>\<^bold>1\<close>)
  assumes left_neutral [simp]: "\<^bold>1 \<^bold>* a = a"
  assumes right_neutral [simp]: "a \<^bold>* \<^bold>1 = a"

locale comm_monoid = abel_semigroup +
  fixes z :: 'a (\<open>\<^bold>1\<close>)
  assumes comm_neutral: "a \<^bold>* \<^bold>1 = a"

begin
sublocale monoid
  by standard (simp_all add: commute comm_neutral)
end

locale group = semigroup +
  fixes z :: 'a (\<open>\<^bold>1\<close>)
  fixes inverse :: "'a \<Rightarrow> 'a"
  assumes group_left_neutral: "\<^bold>1 \<^bold>* a = a"
  assumes left_inverse [simp]:  "inverse a \<^bold>* a = \<^bold>1"

begin
lemma left_cancel [simp]: "a \<^bold>* b = a \<^bold>* c \<longleftrightarrow> b = c"
proof
  assume "a \<^bold>* b = a \<^bold>* c"
  then have "inverse a \<^bold>* (a \<^bold>* b) = inverse a \<^bold>* (a \<^bold>* c)" by simp
  then have "(inverse a \<^bold>* a) \<^bold>* b = (inverse a \<^bold>* a) \<^bold>* c"
    by (simp only: assoc)
  then show "b = c" by (simp add: group_left_neutral)
qed simp

sublocale monoid
proof
  fix a
  have "inverse a \<^bold>* a = \<^bold>1" by simp
  then have "inverse a \<^bold>* (a \<^bold>* \<^bold>1) = inverse a \<^bold>* a"
    by (simp add: group_left_neutral assoc [symmetric])
  with left_cancel show "a \<^bold>* \<^bold>1 = a"
    by (simp only: left_cancel)
qed (fact group_left_neutral)

lemma inverse_unique [simp]:
  assumes "a \<^bold>* b = \<^bold>1"
  shows "inverse a = b"
proof -
  from assms have "inverse a \<^bold>* (a \<^bold>* b) = inverse a"
    by simp
  then show ?thesis
    by (simp add: assoc [symmetric])
qed

lemma inverse_neutral [simp]: "inverse \<^bold>1 = \<^bold>1"
  by (rule inverse_unique) simp

lemma inverse_inverse [simp]: "inverse (inverse a) = a"
  by (rule inverse_unique) simp

lemma right_inverse [simp]: "a \<^bold>* inverse a = \<^bold>1"
proof -
  have "a \<^bold>* inverse a = inverse (inverse a) \<^bold>* inverse a"
    by simp
   also have "inverse (inverse a) \<^bold>* inverse a = \<^bold>1"
     by (rule left_inverse)
   then show ?thesis by simp
 qed

lemma right_cancel: "b \<^bold>* a = c \<^bold>* a \<longleftrightarrow> b = c" 
proof 
  assume "b \<^bold>* a = c \<^bold>* a"
  then have "b \<^bold>* a \<^bold>* inverse a = c \<^bold>* a \<^bold>* inverse a"
    by simp
  then show "b = c"
    by (simp add: assoc)
qed simp

section \<open>Our Additions\<close>
lemma unique_identity:
  assumes "e \<^bold>* a = a"
  shows "e = \<^bold>1"
proof -
  have "e \<^bold>* a = \<^bold>1 \<^bold>* a"
    using assms group_left_neutral by simp
  thus "e = \<^bold>1"
    by (rule right_cancel[THEN iffD1]) (* specifies which direction to apply the right cancel lemma*)
qed

end

section \<open>From Library\<close>

class zero =
  fixes zero :: 'a  (\<open>0\<close>)

class one =
  fixes one  :: 'a  (\<open>1\<close>)

class plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>+\<close> 65)

class  minus =
  fixes minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>-\<close> 65)

class times =
  fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>*\<close> 70)

class semigroup_add = plus +
  assumes add_assoc: "(a + b) + c = a + (b + c)"
begin

sublocale add: semigroup plus
  by standard (fact add_assoc)

declare add.assoc [algebra_simps]

end
class ab_semigroup_add = semigroup_add +
  assumes add_commute: "a + b = b + a"

begin
sublocale add: abel_semigroup plus
  by standard (fact add_commute)

declare add.commute [algebra_simps]
  add.left_commute [algebra_simps]

lemmas add_ac = add.assoc add.commute add.left_commute
end


class semigroup_mult = times +
  assumes mult_assoc: "(a * b) * c = a * (b * c)"

begin
sublocale mult: semigroup times
  by standard (fact mult_assoc)

declare mult.assoc [algebra_simps]
end

class monoid_mult = one + semigroup_mult +
  assumes mult_1_left: "1 * a  = a"
    and mult_1_right: "a * 1 = a"

class comm_monoid_add = zero + ab_semigroup_add +
  assumes add_0: "0 + a = a"

lemma one_reorient: "1 = x \<longleftrightarrow> x = 1"
  by (auto)

class ab_group_add = minus  + comm_monoid_add +
  assumes ab_left_minus: "(0 - a) + a = 0"
  assumes ab_diff_conv_add_uminus: "a - b = a + (0 - b)"

subsection \<open>Semirings and rings\<close>

class semiring = ab_semigroup_add + semigroup_mult +
  assumes distrib_right : "(a + b) * c = a * c + b * c"
  assumes distrib_left: "a * (b + c) = a * b + a * c"

class mult_zero = times + zero +
  assumes mult_zero_left [simp]: "0 * a = 0"
  assumes mult_zero_right [simp]: "a * 0 = 0"

begin
lemma mult_not_zero: "a * b \<noteq> 0 \<Longrightarrow> a \<noteq> 0 \<and> b \<noteq> 0"
  by auto
end

class ring = semiring + ab_semigroup_add

end