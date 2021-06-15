# Abstract
Relational formats describe which relations may be established by which other
relations.  Transition systems describe which states may be reached by which
other states.  We describe a safety-property-preserving translation between a
relational program description and a transition system description.  We
identify a state for each element of a relation; transitions through the system
corresponding to relation derivations.


# Relational CHC description - what relations elements can you establish

A relational CHC description is a set of rules and a query. The rules are horn
clauses which tell you how you can establish certain relations. A relation may
be established outright or conditionally.

Here is an example Horn program.

    entry:
    i = 0
    bb0: do { i += 3; }
    while (i < 5)
    bb1: assert(i < 7)
    either goes to bbsafe or bbunsafe

The labels are translated into relations. Each relation be defined in terms of
program variables. In this example, relations bb0 and bb1 use the current
values for i.

    (declare-rel entry ())
    (declare-rel bb0 (Int))
    (declare-rel bb1 (Int))
    (declare-rel bbsafe ())
    (declare-rel bbunsafe ())

We use i and x as (universally-quantified) variables inside the rules.
Essentially, these variables are temporaries.

    (declare-var i Int)
    (declare-var x Int)

The rules correspond to steps in the execution of the program. We can always
get to entry, so we have a single rule for that. Each (rule (=> X Y)) has a
head Y and a body X. The body is the condition upon which the head Y is
established.

    (rule entry)
    (rule (=> (and entry (= i 0))
              (bb0 i)))
    (rule (=> (and (bb0 i) (< i 5) (= x (+ i 3)))
              (bb0 x)))
    (rule (=> (and (bb0 i) (not (< i 5)))
              (bb1 i)))
    (rule (=> (and (bb1 i) (< i 7))
              bbsafe))
    (rule (=> (and (bb1 i) (not (< i 7)))
              bbunsafe))
    (query bbunsafe)

For example, in these rules, we can establish the relation `(bb0 0)` as long as
we're at `entry` and `i=0`. Note that `i` is universally quantified, so `i=0`
is really defining what `i` we're talking about.

In order to establish the query (`bbunsafe`), we would reason backward to see
what allows us to establish it (the last rule). Recursively, we would reason
backwards again to establish that rule's body, etc.



## Constructs in the CHC language

    (declare-var [var] [sort]) Declare a variable that is universally quantified in Horn clauses.
    (declare-rel [relation-name] ([sorts])) Declare relation signature. Relations are uninterpreted.
    (rule [universal-horn-formula]) Assert a rule or a fact as a universally quantified Horn formula.
    (query [relation-name]) Pose a query. Is the relation non-empty.
    (set-predicate-representation [function-name] [symbol]+) Specify the representation of a predicate.

From here: \url{https://rise4fun.com/z3/tutorialcontent/fixedpoints}


# Transition system description - what states can you reach

A transition system description talks about how to visit states that are
defined on the system's state variables. Since we want to relate Horn systems
to transition systems, we have to show what it means to establish a relation.

Briefly, we associate a primary input with every var. For a relation of arity
k, we associate k+1 state variables. One variable is Boolean, the others
correspond to the sorts of the relation's signature. Every `rule` corresonds to
a transition in the transition relation. Query corresponds to the safety
property.


## Translation rules
Recall that a transition system is defined over (X, Y, X') using formulas I, T,
P. Initially the variable X, Y, X' are empty and I, T, P, are true.

    (declare-var [var] [sort]) Declare a variable that is universally quantified in Horn clauses.

The translation of this adds a variable `[var]` to Y.
    
    (declare-rel R ([sorts])) Declare relation signature. Relations are uninterpreted.

First, create a Boolean state variable `R`.  For each formal parameter position
`i` of `R`, associate to it a unique state variable `Ri`.

In our encoding, when the transition system steps into a state where the
indicator variable `R` is true and its argument variables satisfy `R1 = a1`,
`R2 = a2`, ..., `Rn = an`, then the relation `(R a1 .. an)` is established.
    
    (rule [universal-horn-formula]) Assert a rule or a fact as a universally quantified Horn formula.

A rule is translated to a conjunction over current and next states. The
conjunction then becomes a a disjunct of $T$. A rule is separated into a _head_
and optional _body_. A relation occurrence's translation depends on whether we are translating the body (which gives conditions) or the head (which gives a result).

These are recursively translated, like so:


    (query [relation-name]) Pose a query. Is the relation non-empty.
    (set-predicate-representation [function-name] [symbol]+) Specify the representation of a predicate.
