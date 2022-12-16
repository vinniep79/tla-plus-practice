----------------------------- MODULE HourClock2 -----------------------------
EXTENDS Naturals

VARIABLE hr

HCini == hr \in (1 .. 12)

\* hr evolves differently than before
\* e.g., 13->14 is allowed in HourClock's HCnxt, but not here
HCnxt2 == hr' = (hr % 12) + 1

\* but given the starting condition it doesn't matter so HC and HC2 are 
\* equivalent
HC2 == HCini /\ [][HCnxt2]_hr
-----------------------------------------------------------------------------

THEOREM HC2 => []HCini

=============================================================================
\* Modification History
\* Last modified Fri Dec 16 18:33:35 EST 2022 by Vinnie
\* Created Fri Dec 16 18:28:13 EST 2022 by Vinnie
