// Dafny coursework 2024
//
// Authors: John Wickerson
//
// Changelog:
// * 5-Nov: "Task 5" was mis-labelled as "Task 4" below; now fixed.

type symbol = int
type literal = (symbol,bool)
type clause = seq<literal>
type query = seq<clause>
type valuation = map<symbol,bool>

// extracts the set of symbols from a given clause
function symbols_clause(c:clause) : set<symbol>
  ensures (forall xb :: xb in c ==> xb.0 in symbols_clause(c))
  ensures (forall x :: (x in symbols_clause(c)) ==> (exists b :: (x,b) in c))
{
  if c == [] then {} else
  assert forall xb :: xb in c ==> xb in {c[0]} || xb in c[1..];
  {c[0].0} + symbols_clause(c[1..])
}

// extracts the set of symbols from a given query
function symbols(q:query) : set<symbol>
{
  if q == [] then {} else
  symbols(q[1..]) + symbols_clause(q[0])
}

// evaluates the given clause under the given valuation
predicate evaluate_clause(c:clause, r:valuation) {
  exists xb :: (xb in c) && (xb in r.Items)
}

// evaluates the given query under the given valuation
predicate evaluate(q:query, r:valuation)
{
  forall i :: 0 <= i < |q| ==> evaluate_clause(q[i], r)
}

///////////////////////////////////
// TASK 1: Duplicate-free sequences
///////////////////////////////////

// holds if a sequence of symbols has no duplicates
predicate dupe_free(xs:seq<symbol>)
{
  forall i,j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
}


// Part (a): reversing a dupe-free sequence (recursive implementation)
method rev(xs:seq<symbol>)
  returns (ys:seq<symbol>)
  requires dupe_free(xs)
  ensures dupe_free(ys)
  ensures |xs| == |ys|
  ensures forall i :: 0<= i < |xs| ==> ys[i] == xs[|xs| - i - 1]
{
  if (xs == []) {
    ys := [];
  } else {
    ys := rev(xs[1..]);
    ys := ys + [xs[0]];
  }
}

// Part (b): reversing a dupe-free sequence (iterative implementation)
method rev2(xs:seq<symbol>)
  returns (ys:seq<symbol>)
  requires dupe_free(xs)
  ensures dupe_free(ys)
  ensures |xs| == |ys|
  ensures forall i :: 0<= i < |xs| ==> ys[i] == xs[|xs| - i - 1]
{
  var i:= |xs|-1;
  ys:=[];
  while i>=0
    invariant -1 <= i < |xs|
    invariant |ys| == |xs| - i - 1
    invariant forall i :: 0 <= i < |ys| ==> ys[i] == xs[|xs| - i -1]
  {
    ys:= ys + [xs[i]];
    i:=i-1;
  }
}


//Part (c): concatenating two dupe-free sequences
// This Lemma would NOT hold if we had common values in xs and ys eg xs = [1,2,3] ys = [2,3,4] although both are dupe free, their concatenation wouldnt be dupe free.
// Therefore a precondition is needed to check that we have no common values before the concatenation
lemma dupe_free_concat(xs:seq<symbol>, ys:seq<symbol>)
  requires dupe_free(xs)
  requires dupe_free(ys)
  requires forall x :: x in xs ==> x !in ys
  requires forall y :: y in ys ==> y !in xs
  ensures dupe_free (xs + ys)
{
  reveal dupe_free();
  var res := xs + ys;
  assert forall i :: 0 <=i <|xs| ==> (res[i] in xs) && (res[i] !in ys);
  assert forall j:: |xs| <= j < |res| ==> (res[j] !in xs) && (res[j] in ys);
}

//////////////////////////////////////////
// TASK 2: Extracting symbols from queries
//////////////////////////////////////////

// remove the given set of symbols from a clause
function remove_symbols_clause(c:clause, xs:set<symbol>) : clause
  ensures symbols_clause(remove_symbols_clause(c, xs)) == symbols_clause(c) - xs
  ensures if xs * symbols_clause(c) == {}
          then |remove_symbols_clause(c, xs)| == |c|
          else |remove_symbols_clause(c, xs)| < |c|
{
  if c == [] then [] else
  var c' := remove_symbols_clause(c[1..], xs);
  if c[0].0 in xs then c' else [c[0]] + c'
}

// remove the given set of symbols from a query
function remove_symbols(q:query, xs:set<symbol>) : (query)
  ensures symbols(remove_symbols(q, xs)) == symbols(q) - xs
  ensures |remove_symbols(q, xs)| <= |q|
{
  if q == [] then [] else
  [remove_symbols_clause(q[0], xs)] + remove_symbols(q[1..], xs)
}

// Part (a): extract the sequence of symbols that appear in a clause
function symbol_seq_clause(c:clause) : seq<symbol>
  ensures dupe_free(symbol_seq_clause(c))
  ensures forall x :: x in symbol_seq_clause(c) <==> x in symbols_clause(c)
  decreases symbols_clause(c)
{
  if c == [] then [] else
  var x := c[0].0;
  var c' := remove_symbols_clause(c[1..], {x});
  [x] + symbol_seq_clause(c')
}

// Part (b): extract the sequence of symbols that appear in a query
function symbol_seq(q:query) : seq<symbol>
  ensures dupe_free(symbol_seq(q))
  ensures forall x :: x in symbol_seq(q) <==> x in symbols(q)
  decreases |q|
{
  if q == [] then [] else
  var xs := symbols_clause(q[0]);
  var q' := remove_symbols(q[1..], xs);
  dupe_free_concat(symbol_seq_clause(q[0]),symbol_seq(q'));
  symbol_seq_clause(q[0]) + symbol_seq(q')
}

/////////////////////////////
// TASK 3: Evaluating queries
/////////////////////////////

// evaluate the given clause under the given valuation (imperative version)
method eval_clause (c:clause, r:valuation)
  returns (result: bool)
  ensures result == evaluate_clause(c,r)
{
  var i := 0;
  while (i < |c|)
    invariant 0 <= i <= |c|
    invariant evaluate_clause(c[..i],r) == false
  {
    if (c[i] in r.Items) {
      return true;
    }
    i := i + 1;
  }
  return false;
}

// evaluate the given query under the given valuation (imperative version)
method eval(q:query, r:valuation)
  returns (result: bool)
  ensures result == evaluate(q,r)
{
  var i := 0;
  while (i < |q|)
    invariant 0 <= i <= |q|
    invariant evaluate(q[..i],r) == true
  {
    result := eval_clause(q[i], r);
    if (!result) {
      return false;
    }
    i := i + 1;
  }
  return true;
}

/////////////////////////////////////////////
// TASK 4: Verifying a brute-force SAT solver
/////////////////////////////////////////////

// prepends (x,b) to each valuation in a given sequence
function map_prepend (x:symbol, b:bool, rs:seq<valuation>) : seq<valuation>
{
  if rs == [] then [] else
  [rs[0][x:=b]] + map_prepend(x,b,rs[1..])
}

// constructs all possible valuations of the given symbols
function mk_valuation_seq (xs: seq<symbol>) : seq<valuation>
{
  if xs == [] then [ map[] ] else
  var rs := mk_valuation_seq(xs[1..]);
  var x := xs[0];
  map_prepend(x,true,rs) + map_prepend(x,false,rs)
}

// Part (c): a brute-force SAT solver. Given a query, it constructs all possible
// valuations over the symbols that appear in the query, and then
// iterates through those valuations until it finds one that works.
method naive_solve (q:query)
  returns (sat:bool, r:valuation)
  ensures sat==true ==> evaluate(q,r)
  ensures sat==false ==> forall r:valuation :: r in mk_valuation_seq(symbol_seq(q)) ==> !evaluate(q,r)
{
  var xs := symbol_seq(q);
  var rs := mk_valuation_seq(xs);
  sat := false;
  var i := 0;
  while (i < |rs|)
    invariant 0 <= i <= |rs|
    invariant forall val :: val in rs[..i] ==> evaluate(q,val) == false
  {
    sat := eval(q, rs[i]);
    if (sat) {
      return true, rs[i];
    }
    i := i + 1;
  }
  return false, map[];
}

////////////////////////////////////////
// TASK 5: Verifying a simple SAT solver
////////////////////////////////////////

// This function updates a clause under the valuation x:=b.
// This means that the literal (x,b) is true. So, if the clause
// contains the literal (x,b), the whole clause is true and can
// be deleted. Otherwise, all occurrences of (x,!b) can be
// removed from the clause because those literals are false and
// cannot contribute to making the clause true.
function update_clause (x:symbol, b:bool, c:clause) : query
  ensures query_size([c]) >= query_size(update_clause(x,b,c))
{
  if ((x,b) in c) then [] else [remove_symbols_clause(c,{x})]
}

// This function updates a query under the valuation x:=b. It
// invokes update_clause on each clause in turn.
function update_query (x:symbol, b:bool, q:query) : query
  ensures query_size(q) >= query_size(update_query(x,b,q))
{
  if q == [] then [] else
  var q_new := update_clause(x,b,q[0]);
  var q' := update_query(x,b,q[1..]);
  query_size_law(q_new,q');
  q_new + q'
}

lemma removing_symbol_not_in_clause(c:clause , x : symbol)
  requires x !in symbols_clause(c)
  ensures remove_symbols_clause(c,{x}) == c
{}

lemma update_symbol_not_in_clause(c:clause , x : symbol)
  requires x !in symbols_clause(c)
  ensures update_clause(x,true,c) == [c] && update_clause(x,true,c) == [c]
{
  removing_symbol_not_in_clause(c,x);
}

lemma update_literal_not_in_clause(c:clause , xb : literal)
  requires xb !in c
  ensures update_clause(xb.0,xb.1,c) == [remove_symbols_clause(c,{xb.0})]
{
}

lemma evaluate_clause_associativity(x:symbol, b:bool, r:valuation, c:clause)
  requires x !in r.Keys
  ensures (evaluate_clause(c,r) || ((x,b) in c)) == evaluate_clause(c,r[x:=b])
{
  if evaluate_clause(c, r) {
    // Case 1: evaluate_clause(c, r) = true
    assert evaluate_clause(c, r[x := b]);
  } else {
    // Case 2: evaluate_clause(c, r) = false
    if (x, b) in c {
      // Subcase 2a: (x, b) is in c
      assert evaluate_clause(c, r[x := b]);
    } else {
      // Subcase 2b: (x, b) is not in c
      assert forall lit :: lit in c ==> lit != (x, b); // Ensure no dependency on (x, b)
      assert !evaluate_clause(c, r[x := b]); // Confirm equivalence
    }
  }
}


lemma evaluating_clause_removal(x:symbol, b:bool, r:valuation, c:clause)
  requires x !in r.Keys
  ensures evaluate_clause(c, r) == evaluate_clause(remove_symbols_clause(c, {x}), r)
{}


lemma evaluate_update_clause(x:symbol, b:bool, r:valuation, c:clause)
  requires x !in r.Keys
  ensures evaluate (update_clause (x,b,c) , r) == evaluate_clause (c, r[x:=b])
{
  if ((x,b) in c){
    // if this is the case then update_clause will return an empty query
    assert update_clause (x,b,c) ==[];
    // evaluating an empty query is always true
    assert evaluate ([] , r) == true;
    // since we know (x,b) is in c we also know this is true
    assert evaluate_clause (c, r[x:=b]) == true;
    // our lemma holds
    assert evaluate (update_clause (x,b,c) , r) == evaluate_clause (c, r[x:=b]);
  }
  else{
    if (x in symbols_clause(c)){
      // in this case we wil have (x, !b) ONLY in the clause and all x will be removed as they contribute nothing
      // Here we show that updating the clause is the same as removing all occurences of x, we therefore guarantee x has no effect on valuation
      assert (x,!b) in c;
      assert x !in symbols(update_clause(x, b, c));
      evaluate_clause_associativity(x,b,r,c);
      evaluating_clause_removal(x,b,r,c);
      //finally
      assert evaluate (update_clause (x,b,c) , r) == evaluate_clause (c, r[x:=b]);
    }
    else{
      // Now this is the case where the clause doesnt even contain x
      assert forall val :: val in symbol_seq_clause( c ) ==> val !=x;
      assert forall val :: val in symbol_seq( update_clause (x,b,c) ) ==> val !=x;
      removing_symbol_not_in_clause(c,x);
      //finally
      assert evaluate (update_clause (x,b,c) , r) == evaluate_clause (c, r[x:=b]);
    }
  }
}


lemma evaluate_query_associativity(q: query, r: valuation)
  requires |q| >= 0
  ensures evaluate(q, r) == (if |q| > 0 then (evaluate_clause(q[0], r) && evaluate(q[1..], r)) else true)
{}

lemma update_clause_query_associativity(x:symbol, b:bool, r:valuation, q:query)
  requires |q| > 0
  ensures evaluate(update_query(x, b, q), r) == (evaluate(update_clause(x, b, q[0]), r) && evaluate(update_query(x, b, q[1..]), r))
{
  evaluate_query_associativity(update_query(x,b,q),r);
  // !!! ????
  assert update_query(x, b, q[1..]) == ([] + update_query(x, b, q[1..]));

}

// Updating a query under the valuation x:=b is the same as updating
// the valuation itself and leaving the query unchanged.
lemma evaluate_update_query(x: symbol, b: bool, r: valuation, q: query)
  requires x !in r.Keys
  ensures evaluate(update_query(x, b, q), r) == evaluate(q, r[x := b])
{
  if |q| == 0 {
    assert evaluate(update_query(x, b, q), r) == evaluate(q, r[x := b]);
  }
  else{
    evaluate_update_clause(x, b, r, q[0]);
    update_clause_query_associativity(x,b,r,q);
    //finally
    assert evaluate(update_query(x, b, q), r) == evaluate(q, r[x := b]);
  }
}


// A simple SAT solver. Given a query, it does a three-way case split. If
// the query has no clauses then it is trivially satisfiable (with the
// empty valuation). If the first clause in the query is empty, then the
// query is unsatisfiable. Otherwise, it considers the first symbol that
// appears in the query, and makes two recursive solving attempts: one
// with that symbol evaluated to true, and one with it evaluated to false.
// If neither recursive attempt succeeds, the query is unsatisfiable.
function query_size(q:query):nat
{
  if(q==[]) then 0 else |q[0]| + query_size(q[1..])
}

lemma query_size_law(q1: query, q2: query)
  ensures query_size(q1) + query_size(q2) == query_size(q1 + q2)
{
  if q1 == [] {
    assert query_size(q1) + query_size(q2) == query_size(q2);
    assert (q1+q2) == q2;
    assert query_size(q1 + q2) == query_size(q2);
  }
  else {
    var h := q1[0];
    var t := q1[1..];
    // dafny can suck my nuts!
    assert q1 + q2 == [h] + (t + q2);
  }
}

lemma decrease_after_update(x: symbol, b: bool, q: query)
  requires |q|>0
  requires x in symbols_clause(q[0])
  ensures query_size(q)>query_size(update_query(x,b,q))
{
  query_size_law(update_clause(x,b,q[0]) , update_query(x,b,q[1..]));
}




method simp_solve (q:query)
  returns (sat:bool, r:valuation)
  ensures sat==true ==> evaluate(q,r)
  ensures sat==false ==> forall r :: !evaluate(q,r)
  decreases query_size(q)
{
  if (q == []) {
    return true, map[];
  } else if (q[0] == []) {
    return false, map[];
  } else {
    var x := q[0][0].0;
    decrease_after_update(x,true,q);
    sat, r := simp_solve(update_query(x,true,q));
    if (sat) {
      r := r[x:=true];
      return;
    }
    decrease_after_update(x,false,q);
    sat, r := simp_solve(update_query(x,false,q));
    if (sat) {
      r := r[x:=false];
      return;
    }
    return sat, map[];
  }
}

method Main ()
{
  var sat : bool;
  var r : valuation;
  var q1 := /* (a ∨ b) ∧ (¬b ∨ c) */
            [[(1, true), (2, true)], [(2, false), (3, true)]];
  var q2 := /* (a ∨ b) ∧ (¬a ∨ ¬b) */
            [[(1, true), (2, true)], [(1, false)], [(2, false)]];
  var q3 := /* (a ∨ ¬b) */
            [[(1, true), (2, false)]];
  var q4 := /* (¬b ∨ a) */
            [[(2, false), (1, true)]];

  var symbol_seq := symbol_seq(q1);
  print "symbols = ", symbol_seq, "\n";

  var rs := mk_valuation_seq(symbol_seq);
  print "all valuations = ", rs, "\n";

  sat, r := naive_solve(q1);
  print "solver = naive, q1 result = ", sat, ", valuation = ", r, "\n";

  sat, r := naive_solve(q2);
  print "solver = naive, q2 result = ", sat, ", valuation = ", r, "\n";

  sat, r := naive_solve(q3);
  print "solver = naive, q3 result = ", sat, ", valuation = ", r, "\n";

  sat, r := naive_solve(q4);
  print "solver = naive, q4 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q1);
  print "solver = simp, q1 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q2);
  print "solver = simp, q2 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q3);
  print "solver = simp, q3 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q4);
  print "solver = simp, q4 result = ", sat, ", valuation = ", r, "\n";
}
