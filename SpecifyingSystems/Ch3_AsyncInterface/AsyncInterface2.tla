-------------------------- MODULE AsyncInterface2 --------------------------
EXTENDS Naturals
CONSTANT Data
VARIABLE chan

\* Same spec as before, but introducing a chan record to simplify the interface
\* Instead of 3x variables, we have 3x fields on a tuple
TypeInvariant == chan \in [val: Data, rdy: { 0, 1 }, ack: { 0, 1 }]
----------------------------------------------------------------------------
\* Same initial conditions as before, but using the chan record.
Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy

\* Same conditions for Send, but now expressed as an OPERATOR that takes a single argument, d.
\* chan EXCEPT means "everything about chan is unchanged, EXCEPT..."
\* ! is syntactic sugar for chan', so "!.rdy = " is "the next state of ready equals..."
\* @ is syntactic sugar for "the original value", so "...1 - @" is "1 minus the original value of rdy" (chan.rdy)
Send(d) ==  /\ chan.rdy = chan.ack
            /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv == /\ chan.rdy # chan.ack
        /\ chan' = [chan EXCEPT !.ack = 1 - @]
        
\* "There exists some element of data such that Send or Rcv"
Next == (\E d \in Data : Send(d)) \/ Rcv

Spec == Init /\ [][Next]_chan
---------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Mon Dec 19 18:13:03 EST 2022 by Vinnie
\* Created Mon Dec 19 17:55:02 EST 2022 by Vinnie
