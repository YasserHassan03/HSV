theory HSV_tasks_2024 imports Main begin

section \<open> Task 1: Extending our circuit synthesiser with NAND gates. \<close>

text \<open> Datatype for representing simple circuits, extended with NAND gates. \<close>
datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| NAND "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text \<open> Simulates a circuit given a valuation for each input wire. \<close>
fun simulate where
  "simulate (AND c1 c2) \<rho> = ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>))"
| "simulate (OR c1 c2) \<rho> = ((simulate c1 \<rho>) \<or> (simulate c2 \<rho>))"
| "simulate (NAND c1 c2) \<rho> = (\<not> ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>)))"
| "simulate (NOT c) \<rho> = (\<not> (simulate c \<rho>))"
| "simulate TRUE \<rho> = True"
| "simulate FALSE \<rho> = False"
| "simulate (INPUT i) \<rho> = \<rho> i"

text \<open> Equivalence between circuits. \<close>
fun circuits_equiv (infix "\<sim>" 50) where
  "c1 \<sim> c2 = (\<forall>\<rho>. simulate c1 \<rho> = simulate c2 \<rho>)"

text \<open> A transformation that replaces AND/OR/NOT gates with NAND gates. \<close>
fun intro_nand where
  "intro_nand (AND c1 c2) = 
         NAND (NAND (intro_nand c1) (intro_nand c2)) TRUE"
| "intro_nand (OR c1 c2) = 
         NAND (NAND (intro_nand c1) TRUE) (NAND (intro_nand c2) TRUE)"
| "intro_nand (NAND c1 c2) = (
         NAND (intro_nand c1) (intro_nand c2))"
| "intro_nand (NOT c) = NAND (intro_nand c) TRUE"
| "intro_nand TRUE = TRUE"
| "intro_nand FALSE = FALSE "
| "intro_nand (INPUT i) = INPUT i"

(*
definition "c1 = AND (INPUT 0) (INPUT 1)"
definition "c2 = NAND (INPUT 0) (INPUT 1)"
value "intro_nand c1"
*)
text \<open> The intro_nand transformation is sound. Note that there is a 
  (deliberate) bug in the definition above, which you will need to fix 
  before you can prove the theorem below.\<close>
theorem intro_nand_is_sound: "intro_nand c \<sim> c"
  apply (induction c)
  apply auto
  done

text \<open> The only_nands predicate holds if a circuit contains only NAND gates. \<close>
fun only_nands where
  "only_nands (NAND c1 c2) = (only_nands c1 \<and> only_nands c2)"
| "only_nands (INPUT _) = True"
| "only_nands TRUE = True"
| "only_nands FALSE = True"
| "only_nands _ = False"


text \<open> The output of the intro_nand transformation is a circuit that only
  contains NAND gates. Note that there is a (deliberate) bug in the
  definition above, which you will need to fix before you can prove the
  theorem below. \<close>
theorem intro_nand_only_produces_nands:
  "only_nands (intro_nand c)"
  apply (induction c)
  apply auto
  done
 

section \<open> Task 2: Converting numbers to lists of digits. \<close>

text \<open> Turns a natural number into a list of digits in reverse order. \<close>
fun digits10 :: "nat \<Rightarrow> nat list"
where
  "digits10 n = (if n < 10 then [n] else (n mod 10) # digits10 (n div 10))"

value "digits10 42"
text \<open> Every digit is less than 10 (helper lemma). \<close>


lemma t2:"\<forall>d \<in> set (digits10 n). d < 10"
proof (induction n rule : digits10.induct )
  case (1 n)
  then show ?case 
  proof (cases "n<10")
    case True
    then show ?thesis
      by (simp add: "1.prems")
  next
    case False
    have "digits10 n = (n mod 10) # digits10 (n div 10)" 
      by (simp add: False)
    hence "n mod 10 < 10" by auto
    hence " \<forall>d \<in> set (digits10 (n div 10)). d < 10" using 1
      by fastforce
    then show ?thesis
      by (metis \<open>digits10 n = n mod 10 # digits10 (n div 10)\<close> \<open>n mod 10 < 10\<close> set_ConsD)
  qed
qed
 

 
text \<open> Every digit is less than 10. \<close>
corollary 
  "\<forall>d \<in> set (digits10 n). d < 10" using t2
  by blast

theorem digits10_never_empty : "\<forall>n \<in> \<nat> . digits10 n \<noteq> []"
  by simp

text \<open> Task 3: Converting to and from digit lists. \<close>

text \<open> A function that converts a list of digits back into a natural number. \<close>
fun sum10 :: "nat list \<Rightarrow> nat"
where
  "sum10 [] = 0"
| "sum10 (d # ds) = d + 10 * sum10 ds"

value "sum10 [2,4]"

text \<open> Applying digits10 then sum10 gets you back to the same number. \<close>
theorem digits10_sum10_inverse: 
  "sum10 (digits10 n) = n"
  by (induct n rule: digits10.induct,simp)

declare [[linarith_split_limit = 20]]


text \<open> Applying sum10 then digits10 doesnt always return the same number!!! \<close>
lemma digits10_sum10_counterexample:
  "\<exists>ds. digits10 (sum10 ds) \<noteq> ds" 
  by (metis Nats_0 digits10_never_empty sum10.simps(1))

section \<open> Task 4: A divisibility theorem. \<close>



theorem t4 :"\<forall>x a b.([a,b,a,b,a,b] = digits_10 x) \<and> (sum10 [a,b,a,b,a,b] = x) \<Longrightarrow> x mod 37 = 0" 
  by fastforce

 
section \<open> Task 5: Verifying a naive SAT solver. \<close>

text \<open> This function can be used with List.fold to simulate a do-until loop. \<close>
definition until :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a option \<Rightarrow> 'a option" 
  where
  "until p x z == if z = None then if p x then Some x else None else z" 

text \<open> Once the loop condition holds, the return value is fixed. \<close>
lemma until_some: "fold (until p) xs (Some z) = Some z"
  by (induct xs, auto simp add: until_def)

text \<open> If the loop returns None, the condition holds for no element of the input list. \<close>
lemma until_none: "fold (until p) xs None = None \<Longrightarrow> list_all (\<lambda>x. \<not> p x) xs"
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  hence *: "fold (until p) xs (until p a None) = None" by simp
  {
    assume "p a"
    hence "until p a None = Some a" by (simp add: until_def)
    hence "fold (until p) xs (Some a) = None" using * by presburger
    hence False using until_some by (metis option.distinct(1))
  } 
  moreover {
    assume "\<not> p a"
    hence "until p a None = None" by (simp add: until_def)
    hence "fold (until p) xs None = None" using * by presburger
    hence "list_all (\<lambda>x. \<not> p x) xs" by (rule Cons.hyps)
    hence ?case by (simp add: `\<not> p a`)
  } 
  ultimately show ?case by blast
qed

text \<open> If the loop returns Some x, the condition holds for element x of the input list. \<close>
lemma until_none_some: "fold (until p) xs None = Some x \<Longrightarrow> p x \<and> List.member xs x"
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  hence *: "fold (until p) xs (until p a None) = Some x" by simp
  {
    assume "p a"
    hence "until p a None = Some a" by (simp add: until_def) 
    hence "a = x" by (metis * option.inject until_some)
    hence "p x \<and> List.member (a # xs) x" using `p a` in_set_member by force
  } 
  moreover {
    assume "\<not> p a"
    hence "until p a None = None" by (simp add: until_def)
    hence "fold (until p) xs None = Some x" using * by presburger
    hence "p x \<and> List.member (a # xs) x" using Cons.hyps by (simp add: member_rec(1))
  } 
  ultimately show ?case by blast
qed

text \<open> We shall use strings to represent symbols. \<close>
type_synonym symbol = "string"

text \<open> A literal is either a variable or a negated symbol. \<close>
type_synonym literal = "symbol * bool"

text \<open> A valuation is a list of symbols and their truth values. \<close>
type_synonym valuation = "(symbol * bool) list"

text \<open> A clause is a disjunction of literals. \<close>
type_synonym clause = "literal list"

text \<open> A SAT query is a conjunction of clauses. \<close>
type_synonym query = "clause list"

text \<open>Given a valuation, evaluate a clause to its truth value.\<close>
definition evaluate_clause :: "valuation \<Rightarrow> clause \<Rightarrow> bool"
where 
  "evaluate_clause \<rho> c = list_ex (List.member \<rho>) c"

text \<open> Given a valuation, evaluate a query to its truth value. \<close>
definition evaluate :: "query \<Rightarrow> valuation \<Rightarrow> bool"
where 
  "evaluate q \<rho> = list_all (evaluate_clause \<rho>) q"

text \<open> Some sample queries and valuations. \<close>
(* q1 is (a \<or> b) \<and> (\<not>b \<or> c) *)
definition "q1 == [[(''a'', True), (''b'', True)], [(''b'', False), (''c'', True)]]"
(* q2 is (a \<or> b) \<and> (\<not>a \<or> \<not>b) *)
definition "q2 == [[(''a'', True), (''b'', True)], [(''a'', False)], [(''b'', False)]]"
(* q3 is (a \<or> \<not>b) *)
definition "q3 == [[(''a'', True), (''b'', False)]]"
(* q4 is (\<not>b \<or> a) *)
definition "q4 == [[(''b'', False), (''a'', True)]]"
definition "q5 == [[(''a'', True), (''b'', True)]]"
definition "\<rho>1 == [(''a'', True), (''b'', True), (''c'', False)]"
definition "\<rho>2 == [(''a'', False), (''b'', True), (''c'', True)]"

value "evaluate q1 \<rho>1" 
value "evaluate q1 \<rho>2"

text \<open> Construct the list of all possible valuations over the given symbols. \<close>
fun mk_valuation_list :: "symbol list \<Rightarrow> valuation list"
where 
  "mk_valuation_list [] = [[]]"
| "mk_valuation_list (x # xs) = (
     let \<rho>s = mk_valuation_list xs in 
     map ((#) (x, True)) \<rho>s @ map ((#) (x, False)) \<rho>s)"

value "mk_valuation_list [''a'',''b'']"
value "mk_valuation_list [''a'',''b'',''c'']"

fun symbol_of_literal :: "literal \<Rightarrow> symbol"
where
  "symbol_of_literal (x, _) = x"

text \<open> Extract the list of symbols from the given clause. \<close>
definition symbol_list_clause :: "clause \<Rightarrow> symbol list"
where 
  "symbol_list_clause c == remdups (map symbol_of_literal c)"

text \<open> Extract the list of symbols from the given query. \<close>
definition symbol_list :: "query \<Rightarrow> symbol list"
where
  "symbol_list q == remdups (concat (map symbol_list_clause q))"

value "symbol_list q1"
value "symbol_list q2"

text \<open> A naive SAT solver. It works by constructing the list of all
  possible valuations over the symbols that appear in the query, and
  then iterating through that list until it finds the first valuation
  that makes the query true. If none of the valuations make the query
  true, it returns None. \<close>
definition naive_solve :: "query \<Rightarrow> valuation option"
where
  "naive_solve q == 
  let xs = symbol_list q in 
  let \<rho>s = mk_valuation_list xs in
  List.fold (until (evaluate q)) \<rho>s None"

value "naive_solve q1"
value "naive_solve q2"
value "naive_solve q3"
value "naive_solve q4"

text \<open> If the naive SAT solver returns a valuation, then that 
  valuation really does make the query true. \<close>
theorem naive_solve_correct_sat:
  assumes "naive_solve q = Some \<rho>"
  shows "evaluate q \<rho>"
  by (metis assms naive_solve_def until_none_some)

text \<open> If the naive SAT solver returns no valuation, then none of the valuations 
  it tried make the query true. \<close>
theorem naive_solve_correct_unsat:
  assumes "naive_solve q = None"
  shows "\<forall>\<rho> \<in> set (mk_valuation_list (symbol_list q)). \<not> evaluate q \<rho>" 
  by (metis assms list.pred_set naive_solve_def until_none)

section \<open> Task 6: Verifying a simple SAT solver. \<close>

text \<open> Update the clause c by fixing the symbol x to have truth-value b. Recall that a clause is
  a disjunction of literals, so the clause is true if any one of its literals is true. So if
  the clause contains the literal (x,b), which is fixed to be true, then the whole clause 
  becomes true and can be completely removed (replaced with the empty list). And if the clause 
  contains the literal (x, \<not>b), which is fixed to be false, then that literal should be removed 
  from the clause. \<close>
definition update_clause :: "symbol \<Rightarrow> bool \<Rightarrow> clause \<Rightarrow> clause list"
where
  "update_clause x b c = (if List.member c (x, b) then [] else [removeAll (x, \<not> b) c])"

value "update_clause ''a'' True [(''a'', True), (''b'', False), (''c'', True)]"
value "update_clause ''a'' False [(''a'', True), (''b'', False), (''c'', True)]"
value "update_clause ''a'' True [(''a'', True), (''a'', False)]"
value "update_clause ''a'' True [(''a'', False)]"

text \<open> Update a query by fixing the symbol x to have truth-value b. This is done by
  updating each clause independently (using the update_clause function). \<close>
fun update_query :: "symbol \<Rightarrow> bool \<Rightarrow> query \<Rightarrow> query"
where
  "update_query x b [] = []"
| "update_query x b (c # q) = update_clause x b c @ update_query x b q"

value "update_query ''a'' True q1"
value "update_query ''a'' False q1"
value "update_query ''b'' True q1 "
value "update_query ''b'' False q1"

text \<open> Extract the set of symbols that appear in a given clause. \<close>
definition symbols_clause :: "clause \<Rightarrow> symbol set"
where 
  "symbols_clause c \<equiv> set (map symbol_of_literal c)"

text \<open> Extract the set of symbols that appear in a given query. \<close>
definition symbols :: "query \<Rightarrow> symbol set"
where
  "symbols q \<equiv> \<Union> (set (map symbols_clause q))"

value "symbols q1"
value "symbols q2"

text \<open> A simple SAT solver. Given a query, it does a three-way case split. If 
  the query has no clauses then it is trivially satisfiable (with the
   empty valuation). If the first clause in the query is empty, then the
   query is unsatisfiable. Otherwise, it considers the first symbol that 
   appears in the query, and makes two recursive solving attempts: one 
   with that symbol evaluated to true, and one with it evaluated to false.
   If neither recursive attempt succeeds, the query is deemed unsatisfiable. \<close>
function simp_solve :: "query \<Rightarrow> valuation option"
where
  "simp_solve q = (
   case q of
     [] \<Rightarrow> Some []
   | [] # _ \<Rightarrow> None
   | ((x,_) # _) # _ \<Rightarrow> (
     case simp_solve (update_query x True q) of
       Some \<rho> \<Rightarrow> Some ((x, True) # \<rho>)
     | None \<Rightarrow> (
       case simp_solve (update_query x False q) of 
         Some \<rho> \<Rightarrow> Some ((x, False) # \<rho>)
       | None \<Rightarrow> None)))"
by pat_completeness auto
termination 
  sorry

value "update_query ''b'' True (update_query ''a'' True q1)"
value "simp_solve q1"
value "simp_solve q2"
value "simp_solve q3"
value "simp_solve q4"
value "simp_solve q5"


definition domain :: "('a * 'b) list \<Rightarrow> 'a set"
where
  "domain kvs = set (map fst kvs)"



lemma removing_symbol_not_in_clause:
  assumes "(x, b) \<notin> set c"
  shows "removeAll (x, b) c = c"
  using assms
  by auto

lemma update_literal_not_in_clause:
  assumes "(x, b) \<notin> set c"
  shows "update_clause x b c = [removeAll (x,\<not>b) c]" 
  using assms
  by (simp add: in_set_member update_clause_def)

lemma evaluate_clause_associativity:
  assumes xdom: "x \<notin> domain \<rho>"
  shows "(evaluate_clause c \<rho> \<or> (x, b) \<in> set c) = (evaluate_clause c ((x, b) # \<rho>))" 
  using xdom
  using evaluate_clause_def member_def by fastforce

lemma evaluating_clause_removal:
  assumes xdom: "x \<notin> domain \<rho>"
  shows "evaluate_clause c \<rho> = evaluate_clause (removeAll (x,b) c) \<rho>"
  using xdom sorry

lemma evaluate_update_clause:
assumes xdom: "x \<notin> domain \<rho>"
shows "(evaluate (update_clause x b c) \<rho>) = (evaluate_clause c ((x, b) # \<rho>))"
  using xdom unfolding update_clause_def update_clause_def sorry
 

lemma evaluate_update_query: 
  assumes xdom: "x \<notin> domain \<rho>"
  shows "evaluate (update_query x b q) \<rho> = evaluate q ((x, b) # \<rho>)"
  using xdom
proof (induct "x" "b" "q" rule:HSV_tasks_2024.update_query.induct)
  case (1 x b)
  then show ?case 
    using evaluate_def by auto
next
  case (2 x b c q)
  then show ?case 
  proof(cases "List.member c (x, b)")
    case True
    have "evaluate (update_query x b (c # q)) \<rho> = evaluate (update_clause x b c @ update_query x b q) \<rho>" by simp
    also have " ... = evaluate (update_query x b q) \<rho>" using xdom by (simp add: True update_clause_def)
    also have ahmad:"... = evaluate q ((x,b) # \<rho>)" by (simp add: "local.2.hyps" "local.2.prems")
    have omar:"list_all (evaluate_clause ((x, b) # \<rho>)) (c # q) = list_all (list_ex (List.member ((x, b) # \<rho>))) (c # q) "
      using evaluate_clause_def by presburger
    have yazan:"... = evaluate (c # q) ((x, b) # \<rho>)"
      using evaluate_clause_def evaluate_def by presburger
    from omar ahmad yazan show ?thesis 
      using Bex_set True calculation evaluate_clause_def evaluate_def member_def member_rec(1) by fastforce
  next
    case False
      have "evaluate (update_query x b (c # q)) \<rho> = evaluate (removeAll (x, \<not>b) c # update_query x b q) \<rho>" by (simp add: False update_clause_def) 
      also have "...  = evaluate (c # update_query x b q) \<rho>"
        proof (cases "List.member c (x,\<not>b)")
          case True
           have omar:"evaluate (c # update_query x b q) \<rho> = list_all (list_ex (List.member \<rho>)) (c # (update_query x b q))"
             using evaluate_clause_def evaluate_def by presburger
           also have "... = list_all (list_ex (List.member \<rho>)) ((removeAll (x, \<not>b) c) # (update_query x b q))" sorry 
           finally show ?thesis
             by (metis evaluate_clause_def evaluate_def list_all_cong)
        next
        case False
          then show ?thesis by (simp add: in_set_member) 
        qed
    have  "evaluate (update_query x b (c # q)) \<rho> = evaluate (update_clause x b c @ update_query x b q) \<rho>" by simp
    also have " ... = evaluate ([removeAll (x, \<not> b) c]@ update_query x b q) \<rho>" using False update_clause_def by auto
    also have " ... = list_all (evaluate_clause \<rho>) ([removeAll (x, \<not> b) c]@ update_query x b q) " sorry
    also have  " ... = evaluate (c#q) ((x, b) # \<rho>) " sorry
    then show ?thesis
      using \<open>evaluate (update_query x b (c # q)) \<rho> = evaluate (removeAll (x, \<not> b) c # update_query x b q) \<rho>\<close> calculation by blast
qed 

text \<open> If the simple SAT solver returns a valuation, then that 
  valuation really does make the query true. \<close>
theorem simp_solve_sat_correct:
  "simp_solve q = Some \<rho> \<Longrightarrow> evaluate q \<rho>"
  sorry

text \<open> A valuation is deemed well-formed (wf) as long as it does
  not assign a truth-value for the same symbol more than once. \<close>
definition wf_valuation where
  "wf_valuation \<rho> = distinct (map fst \<rho>)"

text \<open> If the simple SAT solver returns no valuation, then 
  there exists no well-formed valuation that can make the 
  query evaluate to true. \<close>
theorem simp_solve_unsat_correct:
  "simp_solve q = None \<Longrightarrow> 
   (\<forall>\<rho>. wf_valuation \<rho> \<longrightarrow> \<not> evaluate q \<rho>)"
  sorry

end