----------------------------- MODULE HourClock -----------------------------
EXTENDS Naturals

\* hr represents the clock's display
\* It may or may not change through successive states
\* Terminology:  State changes are STEPS
VARIABLE hr

\* Initially the clock is showing any hour between 1 and 12, inclusive.
\* Terminology:  Initial PREDICATE
HCini == hr \in (1 .. 12)

\* The next state of hr is hr + 1, as long as hour is not equal to 12, in which 
\* case we want hr to go to 1.
\* Terminiology: Because this forumula contains primed and unprimed variables, it's 
\* an ACTION.
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

\* Terminology:  A STUTTERING STEP leaves the variable unchanged.
\*  i.e., it is not an HCnxt action.

\* Termporal formula:
\* [] "box" asserts that each step satisfies what follows
\* [HCnxt]_hr is shorthand for "HCnxt is true OR hr remains unchanged (stuttering step)
\* HC says "hr starts as a value between 1-12, and its value always evolves as +1 or back to 1,
\* or it remains unchanged."
HC == HCini /\ [][HCnxt]_hr
-----------------------------------------------------------------------------

\* Terminology:  A THEOREM is a temporal formula satisfied by every behavior
\* Since hr started as an integer between 1-12 and only evolves as +1 or back to 1,
\* it's true that hr is always an integer between 1-12.
THEOREM HC => []HCini

=============================================================================
\* Modification History
\* Last modified Fri Dec 16 18:27:33 EST 2022 by Vinnie
\* Created Fri Dec 16 17:33:47 EST 2022 by Vinnie
