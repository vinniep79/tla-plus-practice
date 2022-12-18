--------------------------- MODULE AsyncInterface ---------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES val, rdy, ack

\* Type Invariants are 
\* valid values of variables in a behavior that satisfies the spec
TypeInvariant == 
    /\ val \in Data 
    /\ rdy \in { 0, 1 }
    /\ ack \in { 0, 1 }
    
\* A STATE FUNCTION is an ordinary expression that coan contains variables and constants.  (No primes or [])
\* A STATE PREDICATE is a Boolean-valued state function.
\* An invariant Inv of a specification Spec is a state predicate such that Spec => []Inv is a theorem
\* In plain English:  The invariant is true at all times for the behaviors that satisfy the spec.
\* A variable v has Type T in spec Spec iff v is an element of T is an invariant of the Spec.
\* In plain English a variable has Type T if it's always an element of the set that defines T.

\* Initially:  val can have any value in Data and rdy and ack are both the same bit value.
Init == /\ val \in Data
        /\ rdy \in { 0, 1 }
        /\ ack = rdy

\* Send is only reachable when rdy is equal to ack
\* val becomes a new value from Data and rdy becomes its inverse.  Ack remains unchanged.
Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack
        
\* Rcv is only reachable when rdy is not equal to ack
\* ack becames its inverse, while val and rdy do not change.
Rcv ==  /\ rdy # ack
        /\ ack' = 1 - ack
        /\ UNCHANGED << val, rdy >>

\* The next state is either send or rcv
Next == Send \/ Rcv

Spec == Init /\ [][Next]_<<val, rdy, ack>>

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Sun Dec 18 13:50:58 EST 2022 by Vinnie
\* Created Sun Dec 18 13:29:43 EST 2022 by Vinnie
