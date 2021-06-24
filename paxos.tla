------------------------------- MODULE paxos -------------------------------

EXTENDS Integers

Maximum(S) == 
  (* Probably a bit mind breaking than it needs to be*)
  (* Essentially takes the maximum in the set S*)
  LET Max[T \in SUBSET S] == 
        IF T = {} THEN -1
                  ELSE LET n    == CHOOSE n \in T : TRUE
                           rmax == Max[T \ {n}]
                       IN  IF n \geq rmax THEN n ELSE rmax
  IN  Max[S]
   
CONSTANT RM, Acceptor, Majority, Ballot



ASSUME
  /\ Ballot \subseteq Nat
  /\ 0 \in Ballot
  /\ Majority \subseteq SUBSET Acceptor
  /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}
    
Messages ==
  [type: {"phase1a"}, ins : RM, bal: Ballot \ {0}]
    \cup
  [type: {"phase1b"}, ins : RM, mbal: Ballot, bal: Ballot \cup {-1}, val: {"prepared", "aborted", "none"}, acc: Acceptor]
    \cup
  [type: {"phase2a"}, ins: RM, bal: Ballot, val: {"prepared", "aborted", "none"}]
    \cup
  [type: {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot, val : {"prepared", "aborted"}]
    \cup
  [type: {"Commit", "Abort"}]
  
VARIABLES rmState, aState, msgs

PCTypeOk == 
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState \in [RM -> [Acceptor -> [mbal : Ballot,
                                    bal  : Ballot \cup {-1},
                                    val  : {"prepared", "aborted", "none"}]]]
  /\ msgs \subseteq Messages
 
 
  
 ========================================
\* Modification History
\* Last modified Thu Jun 24 20:03:10 AEST 2021 by Isitha Subasinghe
\* Created Thu Jun 24 19:28:01 AEST 2021 by Isitha Subasinghe

