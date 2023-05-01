---- MODULE readwriter ----
EXTENDS TLC, Integers, Sequences

CONSTANTS NULL, Writers, Readers

RangeOf(f, d) == {f[arg]: arg \in d}
Range(f) == RangeOf(f, DOMAIN f)

Sym == Permutations(Writers) \union Permutations(Readers)

(*--algorithm readwriter
variables
    queue = <<>>;
    received = {};

define
    TypeInvariant ==
        /\ \A m \in Range(queue): m \in Writers
        /\ \A m \in received: m \in Writers

    AllDone ==
        \A t \in Writers \union Readers:
            pc[t] = "Done"

    IsCorrect == AllDone => received = Writers
end define;

process writer \in Writers
begin
    AddToQueue:
        queue := Append(queue, self)
end process;

process reader \in Readers
variables
    msg = NULL
begin
    ReadFromQueue:
        await queue # <<>> \/ received = Writers;
        if queue # <<>> then
            msg := Head(queue);
            queue := Tail(queue);
        end if;
    ProcessMsg:
        if msg # NULL then
            received := received \union {msg};
            msg := NULL;
            goto ReadFromQueue;
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "97092e71" /\ chksum(tla) = "501104da")
VARIABLES queue, received, pc

(* define statement *)
TypeInvariant ==
    /\ \A m \in Range(queue): m \in Writers
    /\ \A m \in received: m \in Writers

AllDone ==
    \A t \in Writers \union Readers:
        pc[t] = "Done"

IsCorrect == AllDone => received = Writers

VARIABLE msg

vars == << queue, received, pc, msg >>

ProcSet == (Writers) \cup (Readers)

Init == (* Global variables *)
        /\ queue = <<>>
        /\ received = {}
        (* Process reader *)
        /\ msg = [self \in Readers |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self \in Writers -> "AddToQueue"
                                        [] self \in Readers -> "ReadFromQueue"]

AddToQueue(self) == /\ pc[self] = "AddToQueue"
                    /\ queue' = Append(queue, self)
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << received, msg >>

writer(self) == AddToQueue(self)

ReadFromQueue(self) == /\ pc[self] = "ReadFromQueue"
                       /\ queue # <<>> \/ received = Writers
                       /\ IF queue # <<>>
                             THEN /\ msg' = [msg EXCEPT ![self] = Head(queue)]
                                  /\ queue' = Tail(queue)
                             ELSE /\ TRUE
                                  /\ UNCHANGED << queue, msg >>
                       /\ pc' = [pc EXCEPT ![self] = "ProcessMsg"]
                       /\ UNCHANGED received

ProcessMsg(self) == /\ pc[self] = "ProcessMsg"
                    /\ IF msg[self] # NULL
                          THEN /\ received' = (received \union {msg[self]})
                               /\ msg' = [msg EXCEPT ![self] = NULL]
                               /\ pc' = [pc EXCEPT ![self] = "ReadFromQueue"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << received, msg >>
                    /\ queue' = queue

reader(self) == ReadFromQueue(self) \/ ProcessMsg(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Writers: writer(self))
           \/ (\E self \in Readers: reader(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
