---- MODULE helloworld ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS S

ASSUME Cardinality(S) > 0

SymS == Permutations(S)

(*--algorithm dup
variables
    seq \in [1..Cardinality(S) -> S];
    idx = 1;
    seen = {};
    is_uniq = TRUE;

define
    TypeInvariant ==
        /\ is_uniq \in BOOLEAN
        /\ seen \subseteq S
        /\ idx \in 1..Len(seq)+1

    IsUniq(s) ==
        \A i, j \in 1..Len(s):
            i # j => s[i] # s[j]

    IsCorrect == pc = "Done" => is_uniq = IsUniq(seq)
end define;

begin
    Iterate:
        while idx <= Len(seq) do
            if seq[idx] \in seen then
                is_uniq := FALSE;
            else
                seen := seen \union {seq[idx]};
            end if;
            idx := idx + 1;
        end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8162b28e" /\ chksum(tla) = "af5a31ef")
VARIABLES seq, idx, seen, is_uniq, pc

(* define statement *)
TypeInvariant ==
    /\ is_uniq \in BOOLEAN
    /\ seen \subseteq S
    /\ idx \in 1..Len(seq)+1

IsUniq(s) ==
    \A i, j \in 1..Len(s):
        i # j => s[i] # s[j]

IsCorrect == pc = "Done" => is_uniq = IsUniq(seq)


vars == << seq, idx, seen, is_uniq, pc >>

Init == (* Global variables *)
        /\ seq \in [1..Cardinality(S) -> S]
        /\ idx = 1
        /\ seen = {}
        /\ is_uniq = TRUE
        /\ pc = "Iterate"

Iterate == /\ pc = "Iterate"
           /\ IF idx <= Len(seq)
                 THEN /\ IF seq[idx] \in seen
                            THEN /\ is_uniq' = FALSE
                                 /\ seen' = seen
                            ELSE /\ seen' = (seen \union {seq[idx]})
                                 /\ UNCHANGED is_uniq
                      /\ idx' = idx + 1
                      /\ pc' = "Iterate"
                 ELSE /\ pc' = "Done"
                      /\ UNCHANGED << idx, seen, is_uniq >>
           /\ seq' = seq

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Iterate
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
