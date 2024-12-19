# Memory as a Resource
As with many great problems in human society, the inciting incident comes down to who owns what resources. Computer memory is no different. It is a resource, critical to the operation of all programs, and without rules and regulations on who owns it, things devolve into madness. 

It is important to point out that memory can refer to either memory on the stack or memory on the heap. It is somewhat easier to discuss memory on the heap, however most comparisons can be made to things on the stack.

## C
It is easiest to demonstrate the problems with memory in C.
```c
int* ptr;
int n = 1;
ptr = (int*)malloc(n * sizeof(int));
ptr[0] = 1;
```
This program allocates *n* integers on the heap and returns the address to this allocated memory. We assign this address to the variable *ptr*. The type of *ptr* is an integer pointer. In C a pointer can be though of as an integer offset into memory where the integers live. 

The C concept of a pointer is good because it is what a pointer is in terms of hardware. However consider the following.
```c
int* ptr2
ptr2 = ptr;
```
Now *ptr* and *ptr2* both contain the same integer offset into memory. But which variable is responsible for the integers that were allocated. The answer is its up to the programmer. This is the best in terms of flexibility however, leaving such an important choice up to the programmer is always a bad idea. This is because the programmer is fallible. If a mistake is made similar to the following.
```c
free(ptr2)
printf("%d", ptr[0]);
// segmentation fault
```    
The program fails at runtime. This specific bug is repeatable and obvious. However there are several other bugs with pointers that are more subtle and ultimately come down to the programmer not keeping track of who is responsible for what memory.
## C++
C has no internal way to deal with these pointer problems. Programmers are left to there own brains and there own tools (tools probably written in C)

On the other hand C++ has object oriented programming. For every object in C++ on instantiation a function called a constructer is called. And when that object goes out of scope a function called a constructer is called.
```c++
{ // scope
	std::vector<int> my_ints(); // <-- constructor is called
	my_ints.push_back(1);
} // <-- destructor is called
```
Inside of the constructor and destructor (and other methods) of the *std::vector<T>* class, memory is automatically handled. This is great as the programmer no longer has to worry about it. However what happens in the following example?
```c++
{ // scope
	std::vector<int> my_ints(); // <-- constructor is called
	my_ints.push_back(1);
	std::vector<int> my_ints2 = my_ints;
} // <-- destructor is called
```
Luckily there are no memory bugs here. But this may not do what you wanted. *std::vector< int > my_ints2 = my_ints;* invokes copy semantics. So *my_ints2* contains a deep copy of *my_ints* this works in the current examples as *my_ints* only has one integer. But what if *my_ints* has 40 megabytes worth of integers. With this innocents looking line you are actually doing a very expensive call. There are many ways to mitigate this expense. 
```c++
{ // scope
	std::vector<int> my_ints(); // <-- constructor is called
	my_ints.push_back(1);
	std::vector<int>& my_ints2 = my_ints;
} // <-- destructor is called
```
Here the type of *my_ints2* has been changed to a reference type. *my_ints2* has read and write privileges to the memory stored in *my_ints* but not the responsibility to deallocate said memory.
```c++
{ // scope
	std::vector<int> my_ints(); // <-- constructor is called
	my_ints.push_back(1);
	std::vector<int> const& my_ints2 = my_ints;
} // <-- destructor is called
```
Here *my_ints* only has read privileges to the memory stored in *my_ints*. In these solutions it is clear that *my_ints* retains ownership of the integer list in memory. What *&* and *const&* types are doing is borrowing the memory that is owned my *my_ints*. This is great for a lot of problems but what if we want to change the ownership of the memory. What if we want *my_ints2* to have ownership.
```c++
{ // scope
	std::vector<int> my_ints(); // <-- constructor is called
	my_ints.push_back(1);
	std::vector<int> my_ints2 = std::move(my_ints);
} // <-- destructor is called
```
Here the memory ownership is transferred from *my_ints* to *my_ints2*. Under the hood this does correspond to copying the pointer to the heap from *my_ints* to *my_ints2* however this also tells *my_ints* that when *my_ints.destructor()* is called there is no pointer to deallocate. 

The C++ example is meant to convey the difference between copy, move and borrow semantics. Often memory errors in C++ are caught at compile time. However this assumes that you use these structures that implement these semantics.  For example there is a specific class called *unique_ptr< T >* that does not implement copy semantics, so when an object inside of a unique pointer is used with implicit copy semantics it is caught at compile time. But you still can do whatever you want in C++, there is no rule that says you have to keep track of ownership in this way. In fact the C example also compiles in C++.
## Rust
Rust takes this idea of copy, move, and borrow semantics and moves it all to a compile time issue by **default**. The purpose of this article is to talk about my model of the Rust programming language inside of Coq. And show you how one could prove that memory is safe in rust.
# Rust in Coq
Coq is a functional programming language combined with an engine that proofs are written in. I will attempt to describe how Rust and Coq works by showing you an implementation of a Rust model in Coq. This model is based on a paper from David j Pearce.
## Types in Coq
Often types in coq need do contain themselves. This is sort of like recursion for types. For example
```coq
Inductive lval : Type :=
| LVar (x : string)
| LDeref (w : lval).
```
As you can see the type of *lval* has two constructors. One that is simply a variable name represented as a string. The other is a dereference of some other lval. 
```coq
LDeref( LDeref (LVar "x"))
```
Is a valid type based on this recursive (or inductive) definition.
### *lval* in Rust
An *lval* or left value meaning that is can be put on the left hand side of a assignment statement.
```rust
y = 1; // LVar "y"
*x = 1; // LDeref( LVar "x")
```
These *lval* often resolve to a location in memory. In fact this is exactly what they are meant for in the model. But first we have to talk about how memory is represented.
## Memory in Rust Model
```coq
Definition store := list (location * (partial_value * lifetime)).
```
Lets break this down step by step. At a high level a store contains a mapping from locations to values. This mapping is implemented with functions on top of a list. So the type at the top level is a coq *list*. The elements in this list are a pair inside of a pair. The top level pair is a pairing between a *location* (a string) and a (informal) value. This (informal) value is a pairing between a *partial_value* (which will be defined shortly) and a "lifetime" which is essentially the scope in which this (informal) value exists inside of.
To describe how a function works it is valuable to see an example
```coq
Fixpoint s_get (st : store) (l : location) 
  : option (partial_value * lifetime) :=
  match st with
  | nil => None
  | (cl, pv_l) :: tl => if cl =? l then Some pv_l else s_get tl l
  end.

Definition example_store := ("x", (PVDefined 1, "l")) :: nil.
Compute (s_get example_store "x") : Some (PVDefined 1, "l").
```
Ignoring the definition of *s_get* the *Compute* statement shows that when you call *s_get* on the example store with a specific location. It finds the *(partial_value, lifetime)* associated with the location. The *Some* indicates that the example store has this location defined. If the location was not defined *s_get* would return *None*.

In the model we are defining a program is a pairing between statements and a store. 
## Values in Rust Model
```coq
Inductive value : Type :=
| VUnit
| VInt (n : nat)
| VOwnRef (s : string)
| VBorrowRef (s : string).
```
This is another inductive type that defines what a value can be. In this rust model there are 4 different values possible.

The unit type is essentially a no value value. In Rust if a function returns nothing it returns the Unit value. This is very common in languages with functional elements like Ocaml.

The integer type is implemented with the coq native *nat* type. Which is its own can of worms but corresponds to the way integers are defined in set theory.

Along the move, copy, and borrow semantics the owning reference and borrowing reference correspond to having read and write access (owning ref) or just read access (borrow ref). Similar to *const&* and *&* types in C++. These types contain strings which are memory locations via the definition of a program store. So these types refer to other locations in memory.
## Values can be undefined
```coq
Inductive partial_value : Type :=
  | PVUndefined
  | PVDefined (v : value).
  ```
This inductive types demonstrates that a value inside of a store can either be defined or not. This is equivalent to the definition of a *Some v* *None* type in other functional languages.
## Terms in Rust Model
Terms are like the small parts of statements. A statements is something the ends in a semicolon in most languages. For example in C++
```c++
std::vector<int> my_ints = {1,2,3};
```
Is a statement that contains terms like *variable name* and *declaration*. 
```coq
Inductive term : Type :=
  (* t1 ; t2 *)
  | TSeq (t1 t2 : term)
  (* {t} *)
  | TBlock (t : term) (lf : lifetime)
  (* let mut x = t *)
  | TDeclaration (x : string) (t : term)
  (* w = t *)
  | TAssignment (w : lval) (t : term)
  (* box t *)
  | TBox (t : term)
  (* &w *)
  | TBorrow (w : lval)
  (* &mut w *)
  | TMutBorrow (w : lval)
  (* w *)
  | TMove (w : lval)
  (* w.copy() *)
  | TCopy (w : lval)
  (* v *)
  | TValue (v : value).
```
There are 10 different possible terms in this model of Rust. 
#### TValue
This is just a value.
#### TBox
Indicates that the term inside is on the heap.
#### TSeq
Is a combination of two terms with a semicolon. 
#### TBlock
A scope
#### TDeclaration and TAssignment
These are the most recognizable statements in the language. Declare corresponds to allocating something new in the store. and assignment corresponds to changing the (informal) value of an already defined in the store.
#### TCopy TMove TMutBorrow TBorrow
These are the explicate semantics inside of rust. With an *lval* you can do 4 things. Copy it, move its ownership, borrow read access, or mutably borrow read and write access.

For example you could borrow read access of a *lval* and give it to a new variable via
```coq
TDeclaration "y" (TBorrow (LVar "x")).
```
## Small step operational semantics
Now that we have defined the notions of a program store, values, and terms. We can talk about how Rust operates when being evaluated. In formal language this is called Rust *operational semantics*. 
#### Small vs Large step operational semantics
Large step would be executing an entire line of a program in one step. This is practical for less complex languages (like Imp) but for languages like Rust we must evaluate small parts of a program line at a time.

### *loc* and Other Semantic functions
We are going to start off with a simple semantic function called *loc*. This function takes a program store, *lval* and returns a *location*. This function will not work all the time due to the fact that our program store does not contain all locations. So instead of a function we must define a partial function. Technically returning a *Some* *None* type is a partial function. But because we are going to try to prove that a program reduces we are going to define an inductive function
#### Inductive functions
An inductive function defines a few rules that can be applied to a proof state. If a rule applies in some state it entails consequences that also must be proved.
```coq
Inductive loc : store -> lval -> location -> Prop :=
| Loc_Var : forall (st : store) (var_loc : string),
	(
	exists (pvl : partial_value * lifetime),
	s_get st var_loc = Some pvl
	) ->
	loc st (LVar var_loc) var_loc
| Loc_Deref :
	forall (st : store) (l lw: location) (w : lval) ,
	(
	exists (lf : lifetime), (
	s_get st lw = Some (# (VBorrowRef l), lf) \/
	s_get st lw = Some (# (VOwnRef l), lf))
	) ->
	loc st w lw ->
	loc st (LDeref w) l.
```
*loc* has two rules. *Loc_Var* applies if a proof state is at *loc st (LVar var_loc) var_loc*. This means that if the proof state has the *loc* function applied to some store *st* and an *lval* which is a *LVar* then *loc* evaluates to the variable name inside of the *lval*.

*Loc_Var* applying correctly means that you must also prove that the *s_get* function applied to the state *st* and location *var_loc* must return a partial_value * location.

*Loc_Deref* is similar but it semantically implements what a dereference means. Basically a dereference is value if there is a location for the *lval* inside of the dereference, and if that location points to a owning or borrowing reference.

In other words you can only dereference an *lval* if is points to a reference in the program store. And if that *lval* is also valid.

I will be honest and say that the semantics only get more complex from here as implemented in coq. It is much easier to talk about them in terms of informal semantics. This is also how they are talked about in the Pearce paper. These new definitions will be my version from the paper.
| Letter | Type|
|  --------  |  -------  |
| S | program store |
| w | lval |
| v | value |
| pv | partial value |
| < . >^m | lifetime |


#### *loc*
```
loc(S, x) = lx 
loc(S, ∗w) = l where loc(S, w) = lw and S(lw) = <VBorrowRef l \/ VOwnRef l>^m
```
#### Read
```
read(S,w) = S(lw) where loc(s,w) = lw
```
#### Write
```
write(S,w,pv) = S[lw -> <(pv)>m] where loc(S,w) = lw and S(lw) is already defined in m scope
```
The bracket notation means we are pushing something new on the program store.
#### Drop
The drop function in the paper is confusing, plus it will not be used heavily. It recursively deallocates owned references from the program store. When we work through the example I will demo what I mean by this.

### Step operational semantics
A step function is generally the inductive function that reduces a pairing between program state and code to another program state and code.

For these rules, the thing below the line will match some proof state. When we apply the rule, the things above the line will also need to be proved true. These rules will make a lot more sense if we have an example to work on. I will introduce the rules as needed as we work through the example.

Here is our program code example and program store.
***
### Step 1
```
  <{
    TDeclaration "x" 1;
    TDeclaration "y" (TBox (TCopy "x"));
    <{
      TDeclaration "z" (TBox 0);
      TAssignment "y" (TBorrow "z");
      TAssignment "y" (TMove "z");
      TMove (LDeref "y");
      Ɛ
    }>^"m"
  }>^"l"
```
| location | partial value | lifetime |
|  --------  |  -------  | -------- |



The brackets indicate scopes and they have an associated lifetime. From the perspective of the semantics all we really have here is a opaque scope with some term inside. So the first step rule will show us how we can step inside of a scope.
#### Rule: BlockA
```
< S1 | t1 --> S2 | t2 >^m
-----------------------------------------
< S1 | <{ t1 }>^m --> S2 | <{ t2 }>^m >^l
```
After we apply this rule we are left to prove `< S1 | t1 --> S2 | t2 >^m`
***
### Step 1.1
Step 1 -> apply BlockA
```
    TDeclaration "x" 1;
    TDeclaration "y" (TBox (TCopy "x"));
    <{
      TDeclaration "z" (TBox 0);
      TAssignment "y" (TBorrow "z");
      TAssignment "y" (TMove "z");
      TMove (LDeref "y");
      Ɛ
    }>^"m"
```
| location | partial value | lifetime |
|  --------  |  -------  | -------- |


Cool! So we moved inside of the first block. Now from the perspective of the reduction a sequence of commands is left associative. So we see the *TDeclaration "x" 1* but the rest of the program is just some other term. So we need a rule that steps into the first command of a sequence of commands
#### Rule: SubSeq
```
< S1 | t1 --> S2 | t2 >^l
--------------------------------------------------------
< S1 | TSeq t1 t3 --> S2 | TSeq t2 t3 >^l
```
Again after we apply this rule we are left to prove ` < S1 | t1 --> S2 | t2 >^l`
*** 
### Step 1.2
Step 1 -> apply BlockA -> apply SubSeq
```
    TDeclaration "x" 1
```
| location | partial value | lifetime |
|  --------  |  -------  | -------- |


Now we are getting somewhere. Because this is a simple declaration (term of RHS is just the value 1) it corresponds to the declaration rule.
#### Rule: Declaration
```
S1[x -> <v>^l)] = S2
--------------------------------------------------------
< S1 | TDeclaration (string x) (value v) --> S2 | () >^l
```
As you can see in the rule, there are effects on the program store.
***
### Step 1.3
Step 1 -> apply BlockA -> apply SubSeq -> apply Declaration
```
    ()
```
| location | partial value | lifetime |
|  --------  |  -------  | -------- |
| "x" | 1 | "l" |


Technically we are left to prove S1 with the proper modification is equal to S2. This is often the case. When we are at the end of the capabilities of the step function we still have to prove some other facts about the program store. If you are interested in how the proof actually finishes you can look at the code in the associated github repo.

The interesting thing that the declaration rule did was give us our first allocation in the program store. It is in lifetime "l" because that is the block we are inside via the BlockA rule.
***
### Step 2
```
<{
    ();
    TDeclaration "y" (TBox (TCopy "x"));
    <{
      TDeclaration "z" (TBox 0);
      TAssignment "y" (TBorrow "z");
      TAssignment "y" (TMove "z");
      TMove (LDeref "y");
      Ɛ
    }>^"m"
}>^"l"
```
| location | partial value | lifetime |
|  --------  |  -------  | -------- |
| "x" | 1 | "l" |


-> apply BlockA
```
    ();
    TDeclaration "y" (TBox (TCopy "x"));
    <{
      TDeclaration "z" (TBox 0);
      TAssignment "y" (TBorrow "z");
      TAssignment "y" (TMove "z");
      TMove (LDeref "y");
      Ɛ
    }>^"m"
```
| location | partial value | lifetime |
|  --------  |  -------  | -------- |
| "x" | 1 | "l" |


From this state we cannot step into the first term of the sequence because it is just the unit value. Intuitively we want to evaluate the next command. To get to a state where this is possible we have the Seq rule.
#### Rule: Seq
```
drop(S1, {v}) = S2
--------------------------------------------------------
< S1 | TSeq (value v) t --> S2 | t >^l
```
***
### Step 2.1
Step 2 -> apply BlockA -> apply Seq
```
    TDeclaration "y" (TBox (TCopy "x"));
    <{
      TDeclaration "z" (TBox 0);
      TAssignment "y" (TBorrow "z");
      TAssignment "y" (TMove "z");
      TMove (LDeref "y");
      Ɛ
    }>^"m"
```
| location | partial value | lifetime |
|  --------  |  -------  | -------- |
| "x" | 1 | "l" |


Note that drop with the unit value did nothing to the program store.

Now we have something much more complicated on the RHS of the declaration. Intuitivly we should make a rule that steps into the RHS of the declaration. This is what the SubDeclaration






#### R_Copy
```
read(S,w) = <v>^m
-----------
< S | TCopy(w) --> S | v >^l
```
#### R_Move
```
read(S1,w) = <v>^m
write(S1,w,PVUndefined) = S2
-----------
< S1 | TMove(w) --> S2 | v >^l
```
#### R_Move
```
read(S1,w) = <v>^m
write(S1,w,PVUndefined) = S2
-----------
< S1 | TMove(w) --> S2 | v >^l
```

# Sources
David J. Pearce. 2021. A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust. ACM Trans. Program. Lang. Syst. 43, 1, Article 3 (March 2021), 73 pages. https://doi.org/10.1145/3443420
