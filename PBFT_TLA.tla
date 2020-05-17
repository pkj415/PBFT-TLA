------------------------------ MODULE PBFT_TLA ------------------------------
\* NOTE - All optimization are tagged with OPT#Num

\* NOTE - For ensuring weak fairness conditions by just declaring it on PBFTNext as below (to stop infinite stuttering), we require
\* each sub step (in PBFTNext) to be disabled ("not enabled") in case it has already been executed and rexecuting it will not change
\* the state.
\*      Declaration as follows - WF_vars(PBFTNext)
\*
\* If the sub-step is left enabled after execution, TLC will allow behaviours that stutter at this sub-step (making it difficult
\* to debug if certain states are eventually reached when adding new functionality in the spec). A workaround to avoiding this is
\* would be to declare weak fairness on each sub-step (as below), but that is cumbersome for two reasons -
\*   1. Required changing the fairness condition when new steps are added, old ones renamed/removed.
\*   2. If a sub-step has a parameters (say process id), then we have to specify WF conditions for all possible sub-steps as below.
\*
\*      Workaround declaration is as follows - \A p_id \in NumProcesses: WF_vars(sendPrePrepares(p_id)) /\ WF_vars(acceptCommitts(p_id)) and so on...
\*
\* This trick is called the WfSimplifier in the spec to succinctly point out conditions added for exactly just this purpose.

\* TODOs -
\*   1. Consider using symmetry sets where ever possible

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT
    \* The total number of processes; Index of each process falls in 0..NumProcesses-1
    NumProcesses,
    \* Set of client commands. The specification (as of now) doesn't bother to model different clients and exactly-one semantics
    \* as mentioned in the paper as this is not relevant to the correctness of the core consensus algorithm.
    ClientCommands,
    \* The maximum view number any process in any behaviour can attain (this is to restrict the allowed behaviours that TLC scans through).
    \* TODO - This can instead be done by specifying a State Constraint when running TLC.
    MaxViewNum,
    \* Maximum number of process failures allowed in the behaviour (this is again to restrict the allowed behaviours that TLC scans through)
    MaxFailures

ASSUME
    /\ NumProcesses >= 4

VARIABLES
    (*
        {[type |-> "PRE-PREPARE", "PREPARE", "COMMIT"
          seq_num |-> 0,
          view_num |-> 0,
          from |-> process id,
          cmd |-> <client command>
         ]}
        Also, all messages (when they have a from field) are assumed to be signed.
    *)
    messages,
    (*
        A function mapping process number to process record -
            [
                view_num |-> 0,
                
                OPT#1 - We don't have to use a sequence for the log, a set suffices (we aren't using the ordering anywhere). Reduce the
                state space.
                log |-> {}, \* This contains all the signed pre-prepare, prepare, commit, new-view, etc  messages from other processes 
                
                status |-> "normal" / "view_change" / "do_view_change_sent"/ "recovering",
                last_active_view_num |-> 0
            ]
    *)
    processState
    (*
        This is used to check that every behaviour conforms with some intended behaviour specified by the LinearizableOrdering spec.
        
        For this, the ordering variable needs to be updated on every step to reflect the ordering of executed commands
        visible to an external user. 
    *)

(* Utility operators *)
QuorumCnt == NumProcesses - (NumProcesses - 1) \div 3

\* This is just a tuple with all variables in the spec (for ease of use in temporal conditions such as Weak Fairness)
vars == <<processState, messages>>

Maximum(S) == IF S = {} THEN 0
              ELSE CHOOSE x \in S: \A y \in S: x >= y

\* isLeader return True if p thinks it is the leader.
isLeader(p) == processState[p].view_num % NumProcesses = p

sendMsgs(msgs) == messages' = messages \cup msgs

\* Fetch a subset of the log entries for a given process based on the params filter.
subsetOfLog(p_id, params) == {log_entry \in processState[p_id].log:
                                  \A field \in DOMAIN params: log_entry[field] = params[field]}

\* Fetch a subset of messages in the network based on the params filter.
subsetOfMsgs(params) == {log_entry \in messages: \A field \in DOMAIN params: log_entry[field] = params[field]}

(* Normal case operation for non-byzantine behaviour *)

sendPrePrepares(p_id) == /\ \E cmd \in ClientCommands:
                              \* Ensure that a PRE-PREPARE wasn't sent earlier for the same client command.
                              /\ \A log_entry \in subsetOfLog(p_id, [type |-> "PRE-PREPARE", view_num |-> processState[p_id].view_num]):
                                      log_entry.cmd # cmd
                              /\ LET
                                     \* Assign the next available sequence number. Assuming the primary doesn't deliberately leave holes.
                                     maxSeqNum == Maximum({log_entry.seq_num: log_entry \in subsetOfLog(p_id,
                                                    [type |-> "PRE-PREPARE", view_num |-> processState[p_id].view_num])})
                                     pre_prepare_msg == [view_num |-> processState[p_id].view_num, type |-> "PRE-PREPARE",
                                                         cmd |-> cmd, seq_num |-> maxSeqNum + 1]
                                 IN
                                    /\ processState' = [processState EXCEPT ![p_id].log = processState[p_id].log \cup {pre_prepare_msg}]
                                    /\ sendMsgs({pre_prepare_msg}) 

acceptPrePrepare(p_id) == /\ \E msg \in messages:
                                /\ msg.type = "PRE-PREPARE"

                                \* Accept a PRE-PREPARE message only if process hasn't accepted one with the same sequence number already. 
                                /\ ~ (msg.seq_num \in {log_entry.seq_num: log_entry \in subsetOfLog(p_id,
                                                         [type |-> "PRE-PREPARE", view_num |-> processState[p_id].view_num])})

                                /\ processState[p_id].view_num = msg.view_num

                                \* Ensure that the client command hasn't been executed before. This is done by checking if the client
                                \* command has ever been committed earlier with a different seq_num (2f+1 COMMIT messages in the log).
                                \* Note that this is done
                                \* differently in reality where the whole log is never preserved (it is preiodically pruned). Since the log
                                \* is pruned, every process maintains a cilent table with nonce (such as timestamp) to ensure the same
                                \* request is not committed again. For the purposes of specifying the core algorithm, pruning the log
                                \* isn't considered (it is just an implementation detail) and we consider figuring out repeats of a
                                \* client request using the local log.

                                /\ ~ (\E <<view_num, seq_num>> \in (0..processState[p_id].view_num) \X (1..Cardinality(ClientCommands)):
                                        Cardinality(subsetOfLog(p_id, [type |-> "COMMIT", view_num |-> view_num,
                                                                       cmd |-> msg.cmd, seq_num |-> seq_num])) >= QuorumCnt)

                                \* We also have to ensure that the client command has not been PRE-PREPARED before in the current view.
                                /\ \A log_entry \in subsetOfLog(p_id, [type |-> "PRE-PREPARE", view_num |-> processState[p_id].view_num]):
                                        log_entry.cmd # msg.cmd

                                /\ LET
                                        prepare_msg == [type |-> "PREPARE", from |-> p_id, view_num |-> processState[p_id].view_num,
                                                        seq_num |-> msg.seq_num, cmd |-> msg.cmd]
                                   IN
                                      /\ processState' = [processState EXCEPT ![p_id].log = processState[p_id].log \cup {msg} \cup {prepare_msg}]
                                      /\ sendMsgs({prepare_msg})

acceptQuorumOfPrepares(p_id) == \E <<cmd, seq_num>> \in ClientCommands \X (1..Cardinality(ClientCommands)):
                                    \* Ensure a PRE-PREPARE for this was received earlier.
                                    \* TODO - Change this to get a new version of PBFT? What if PREPARE messages from 2f+1 processes are received.
                                    \* Still don't fill
                                    \* the slot without the PRE-PEPARE? So stubborn? Note that this optimization will increase
                                    \* the state space. And this optimization is diverges from the protocol in the paper.
                                    /\ subsetOfLog(p_id, [type |-> "PRE-PREPARE", view_num |-> processState[p_id].view_num,
                                                          cmd |-> cmd, seq_num |-> seq_num]) # {}

                                    \* OPT#2 - Ensure a quorum of PREPAREs wasn't accepted already. This helps in two ways -
                                    \*   1. Reducing the state space. We don't care about accepting more than quorum number of PREPAREs
                                    \*      by the same process later in the behaviour. This is not required and just increases the state
                                    \*      space.
                                    \*   2. The WfSimplifier trick
                                    /\ Cardinality(subsetOfLog(p_id, [type |-> "PREPARE", view_num |-> processState[p_id].view_num,
                                                                      seq_num |-> seq_num, cmd |-> cmd])) < QuorumCnt - 1 \* One is PRE-PREPARE

                                    \* OPT#3 - We can further reduce the state space by receiving "exactly" a quorum of PREPAREs in one shot
                                    \* instead of receiving them in different chunks (since these chunks of the PREPARE messages are anyway
                                    \* not used anywhere in the protocol. NOTE that if later a modification is made to the protocol to use
                                    \* partial PREPAREs in any step i.e., non-quorum counts (less or more), this will have to change).
                                    /\
                                        LET SubsetOfPrepares ==
                                              subsetOfMsgs([type |-> "PREPARE", view_num |-> processState[p_id].view_num,
                                                            seq_num |-> seq_num, cmd |-> cmd]) \
                                              \* Don't count own PREPARE
                                              subsetOfMsgs([type |-> "PREPARE", view_num |-> processState[p_id].view_num,
                                                            seq_num |-> seq_num, cmd |-> cmd, from |-> p_id])
                                            commit_msg == [type |-> "COMMIT", from |-> p_id,
                                                           view_num |-> processState[p_id].view_num, cmd |-> cmd, seq_num |-> seq_num]
                                            CntOfPreparesNeeded == IF isLeader(p_id) THEN QuorumCnt - 1 \* It doesn't have an own PREPARE, just a PRE-PREPARE
                                                                   ELSE QuorumCnt - 2 \* One of them is a PRE-PREPARE message and one is own PREPARE
                                        IN
                                            /\ Cardinality(SubsetOfPrepares) >= CntOfPreparesNeeded
                                            /\ LET
                                                   QuorumPrepares == CHOOSE s \in SUBSET SubsetOfPrepares: Cardinality(s) = CntOfPreparesNeeded
                                                IN
                                                   /\ processState' = [
                                                        processState EXCEPT ![p_id].log = processState[p_id].log \cup QuorumPrepares \cup {commit_msg}]
                                                   /\ sendMsgs({commit_msg})

prepared(cmd, seq_num, p_id) == 
    /\ Cardinality(subsetOfLog(p_id, [type |-> "PREPARE", cmd |-> cmd, seq_num |-> seq_num, view_num |-> processState[p_id].view_num])) >= QuorumCnt - 1
    /\ subsetOfLog(p_id, [type |-> "PRE-PREPARE", cmd |-> cmd, seq_num |-> seq_num, view_num |-> processState[p_id].view_num]) # {}

acceptCommits(p_id) == \E <<cmd, seq_num>> \in ClientCommands \X (1..Cardinality(ClientCommands)):
                       \* Ensure that the predicate prepared() as mentioned in the paper is true. If not, don't proceed.
                       \* Because the predicate committed-local() won't be true without predicate() and hence nothing changes
                       \* for the process if it just accepts commits. So to reduce state space accept commits only after prepared()
                       \* is true. TODO - Change this to get a new version of PBFT?
                           /\ prepared(cmd, seq_num, p_id)

                       \* OPT#4 - Ensure a quorum of COMMITs wasn't accepted already. This helps in two ways -
                       \*   1. Reduce the state space by accepting only quorum of commits, more than quorum don't change the protocol in
                       \*      any way. This is similar to the optimization when accepting quorum of PREPAREs.
                       \*   2. The WfSimplifier trick
                           /\ Cardinality(subsetOfLog(p_id, [type |-> "COMMIT", view_num |-> processState[p_id].view_num,
                                                         seq_num |-> seq_num, cmd |-> cmd])) < QuorumCnt

                       \* OPT#5 - We can further reduce the state space by receiving "exactly" a quorum of COMMITs in one shot
                       \* instead of receiving them in different chunks (since these chunks of the COMMIT messages are anyway
                       \* not used anywhere in the protocol. NOTE that if later a modification is made to the protocol to use
                       \* partial COMMITs in any step i.e., non-quorum counts (less or more), this will have to change).
                           /\ LET
                                  SubsetOfCommits ==
                                    subsetOfMsgs([type |-> "COMMIT", view_num |-> processState[p_id].view_num,
                                                  seq_num |-> seq_num, cmd |-> cmd]) \
                                    \* Don't count own COMMIT
                                    subsetOfMsgs([type |-> "COMMIT", view_num |-> processState[p_id].view_num,
                                                  seq_num |-> seq_num, cmd |-> cmd, from |-> p_id])
                              IN
                                  /\ Cardinality(SubsetOfCommits) >= QuorumCnt - 1
                                  /\ LET
                                         QuorumCommits == CHOOSE s \in SUBSET SubsetOfCommits: Cardinality(s) = QuorumCnt - 1
                                     IN
                                         processState' = [processState EXCEPT ![p_id].log = processState[p_id].log \cup QuorumCommits]

\*(* View change steps *)
\*sendStartViewChange(p, new_view_num) == 
\*                      /\ new_view_num > processState[p].view_num
\*                      /\ processState' = [processState EXCEPT ![p].status = "view_change",
\*                                                              ![p].view_num = new_view_num]
\*                      /\ sendMsgs({
\*                            [type |-> "start_view_change",
\*                             to |-> listener,
\*                             from |-> p,
\*                             view_num |-> new_view_num] : listener \in 0..NumProcesses-1 \ {p}
\*                        })
\*
\*sendDoViewChange(p, newLeader) == /\ sendMsgs({
\*                                        [
\*                                            type |-> "do_view_change",
\*                                            from |-> p,
\*                                            to |-> newLeader,
\*                                            view_num |-> processState[p].view_num,
\*                                            log |-> processState[p].log,
\*                                            commit_num |-> processState[p].commit_num,
\*                                            last_active_view_num |-> processState[p].last_active_view_num
\*                                        ]})
\*
\*updateBasedOnStartView(p, msg) == /\ processState' = [processState EXCEPT ![p].status = "normal",
\*                                                                          ![p].commit_num = msg.commit_num,
\*                                                                          ![p].log = msg.log,
\*                                                                          ![p].last_active_view_num = msg.view_num,
\*                                                                          ![p].view_num = msg.view_num]
\*
\*viewChangeTransitions(p) == 
\*                          \/ (
\*                                /\ ~(processState[p].status = "view_change")
\*                                /\ (
\*                                        \* Timer triggered view change. Can't be done by node which thinks its the leader.
\*                                        /\ ~isLeader(p)
\*                                        /\ processState[p].view_num+1 <= MaxViewNum
\*                                        /\ sendStartViewChange(p, processState[p].view_num+1)
\*                                   )
\*                             )
\*                          \/ (
\*                                \* Wait for majority to say view_change and then perform do_view_change
\*                                /\ processState[p].status = "view_change"
\*                                /\ LET mset == {
\*                                            msg \in messages: /\ msg.type = "start_view_change"
\*                                                              /\ msg.view_num = processState[p].view_num
\*                                                              /\ msg.to = p
\*                                        }
\*                                   IN /\ Cardinality(mset) >= NumProcesses \div 2
\*                                /\ sendDoViewChange(p, processState[p].view_num % NumProcesses)
\*                                /\ processState' = [processState EXCEPT ![p].status = "do_view_change_sent"]
\*                             )
\*                          \/ (
\*                                \* Remove? - In view_change status, but got view_change with higher number.
\*                                /\ \* Got larger start_view_change msg from another node.
\*                                   (\E msg \in messages: msg.type = "start_view_change" /\ msg.view_num > processState[p].view_num
\*                                      /\ sendStartViewChange(p, msg.view_num))
\*                             )
\*                          \/ (
\*                                \* In case a start_view msg is received
\*                                /\ (
\*                                      \/ (
\*                                          /\ \E msg \in messages: msg.type = "start_view" /\ msg.view_num > processState[p].view_num
\*                                              /\ updateBasedOnStartView(p, msg)
\*                                         )
\*                                      \/ (
\*                                          \* TODO - Find the invariant to check the case where "normal" wasn't checked when updating with start_view
\*                                          \* message of same view_num
\*                                          /\ ~(processState[p].status = "normal")
\*                                          /\ \E msg \in messages: msg.type = "start_view" /\ msg.view_num = processState[p].view_num
\*                                              /\ updateBasedOnStartView(p, msg)
\*                                         )
\*                                   )
\*                                /\ UNCHANGED <<messages>>
\*                             )
\*
\*\* There is no "to" field in start_view as it is for all replicas.
\*sendStartView(p, v, maxLogMsg) == sendMsgs(
\*                                {
\*                                    [type |-> "start_view",
\*                                     from |-> p,
\*                                     log |-> maxLogMsg.log,
\*                                     view_num |-> v,
\*                                     commit_num |-> maxLogMsg.commit_num]
\*                                }
\*                             )
\*
\*recvMajortiyDoViewChange(p, v) == LET
\*                                        mset == {
\*                                            msg \in messages: /\ msg.type = "do_view_change"
\*                                                              /\ msg.view_num = v
\*                                                              /\ msg.to = p
\*                                        }
\*                                        maxLogMsg == IF mset = {} THEN -1
\*                                            ELSE CHOOSE msg \in mset : \A msg2 \in mset :
\*                                                (\/ (msg.last_active_view_num > msg2.last_active_view_num)
\*                                                 \/ (/\ msg.last_active_view_num = msg2.last_active_view_num /\ Len(msg.log) \geq Len(msg2.log)))
\*                                  IN /\ Cardinality(mset) >= ((NumProcesses \div 2) + 1)
\*                                     /\ processState' = [processState EXCEPT ![p].view_num = v,
\*                                                                             ![p].status = "normal",
\*                                                                             ![p].log = maxLogMsg.log,
\*                                                                             ![p].commit_num = maxLogMsg.commit_num,
\*                                                                             ![p].last_active_view_num = v]
\*                                     /\ sendStartView(p, v, maxLogMsg)

NormalCaseOperation(p_id) ==  \/
                                 \* A process, which thinks it is the leader, sends PRE-PREPARE messages.
                                 /\ isLeader(p_id)
                                 /\ sendPrePrepares(p_id)
                                 /\ UNCHANGED <<>>

                              \/ \* Normal case operation of a replica node.
                                 /\ ~isLeader(p_id)
                                 /\
                                    \/
                                       /\ acceptPrePrepare(p_id)
                                       /\ UNCHANGED <<>>
                              \/
                                 /\ acceptQuorumOfPrepares(p_id)
                                 /\ UNCHANGED <<>>
                              \/
                                 /\ acceptCommits(p_id)
                                 /\ UNCHANGED <<messages>>

\* When a node fails, it loses all data and goes into recovering status.
\*FailNode(p) == 
\*               /\ processState' = [processState EXCEPT ![p].commit_num = 0,
\*                                                       ![p].view_num = 0,
\*                                                       ![p].last_active_view_num = 0,
\*                                                       ![p].log = <<>>,
\*                                                       ![p].status = "recovering"]
\*               /\ sendMsgs(
\*                                {
\*                                    [type |-> "RECOVERY",
\*                                     from |-> p,
\*                                     nonce |-> processState[p].nonce]
\*                                }
\*                             )

\* There are a few ways to handle nonce, this spec follows the first one -
\* 1. Store it on disk and increment it just before a node marks itself "normal".
\* 2. Store it on disk and increment it whenever a node restarts to come into "recovering" status. But this has higher message
\*    complexity considering this scneario - if an already recovering node restarts, it will ignore the RECOVERYRESPONSE
\*    messages from all other nodes since they are from an ealier nonce, even though using those responses would have not violateed
\*    safety. This will require another set of RECOVERYRESPONSE messages.
\* 3. Use a clock value to generate nonce

\*Recover(p) == LET
\*                    \* There might be more than one RECOVERYRESPONSE messages from the same process.
\*                    mset == {
\*                        msg \in messages: /\ msg.type = "RECOVERYRESPONSE"
\*                                          /\ msg.nonce = processState[p].nonce
\*                                          /\ msg.to = p
\*                    }
\*                    sender_set == {p_id \in 0..NumProcesses-1: (\E msg \in mset: msg.from = p_id)}
\*                    maxViewMsg == IF mset = {} THEN <<>>
\*                        ELSE CHOOSE msg \in mset : \A msg2 \in mset :
\*                          \/ (msg.view_num >= msg2.view_num)
\*                    maxViewNum == IF maxViewMsg = <<>> THEN -1
\*                                  ELSE maxViewMsg.view_num
\*              IN 
\*                 /\ processState[p].nonce < MaxFailures
\*                 /\ Cardinality(sender_set) >= ((NumProcesses \div 2) + 1)
\*                 \* Very important - 
\*                 \* Step through all behaviours where process p chooses any of the RECOVERYRESPONSEs from the leader of maxViewNum.
\*                 /\ \E msg \in mset:
\*                      /\ msg.from = maxViewNum % NumProcesses
\*                      /\ msg.view_num = maxViewNum \* This is important, if this check is not included, an older RECOVERYRESPONSE from the leader might be used. TODO - Bring in an invariant
\*                      /\ processState' = [processState EXCEPT ![p].view_num = maxViewNum,
\*                                                              ![p].status = "normal",
\*                                                              ![p].log = msg.log,
\*                                                              ![p].commit_num = msg.commit_num,
\*                                                              ![p].last_active_view_num = maxViewNum,
\*                                                              \* TODO - Consider the case where the process increments
\*                                                              \* the nonce and then fails again. Right now, switching
\*                                                              \* to normal and nonce incrementing is atomic, but
\*                                                              \* it should not be so.
\*                                                              ![p].nonce = processState[p].nonce + 1]

PBFTInit == /\ messages = {}
            /\ processState =
                    [p \in 0..NumProcesses-1 |-> [
                                                    view_num |-> 0,
                                                    log |-> {},
                                                    status |-> "normal", \* normal, view_change, do_view_change_sent, recovering
                                                    last_active_view_num |-> 0
                                                  ]
                    ]

PBFTNext ==
            \/ \* Normal case operation. Executed only when status of process is normal
               /\ \E p \in 0..NumProcesses-1:
                    /\ processState[p].status = "normal"
                    /\ NormalCaseOperation(p)

\*          \/ \* View change transitions. All except "recovering" status nodes can take this step.
\*             /\ \E p \in 0..NumProcesses-1:
\*                  /\ processState[p].status # "recovering"
\*                  /\ viewChangeTransitions(p)
\*
\*          \/ \E p \in 0..NumProcesses-1:
\*               /\ processState[p].status # "recovering"
\*               /\ \E v \in 0..MaxViewNum:
\*                    (
\*                        \* ~isLeader(p) is not kept here because it might happen that a leader again becomes the next leader.
\*                        \* TODO - What safety check would catch such an error?
\*                        /\ (
\*                            \/ v > processState[p].view_num \* TODO - Think of coming up with an invariant which is false in case we just have one condition with v >= processState[p].view_num
\*                            \/ (v = processState[p].view_num /\ ~(processState[p].status = "normal")) 
\*                           )
\*                        /\ v % NumProcesses = p
\*                        /\ recvMajortiyDoViewChange(p, v)
\*                    )

\*          \/ \* Fail a process. It goes to status "recovering"
\*             LET
\*                failed_processes == {p \in 0..NumProcesses-1: processState[p].status = "recovering"}
\*             IN
\*                /\ Cardinality(failed_processes) < ((NumProcesses-1) \div 2)
\*                /\ \E p \in (0..NumProcesses-1 \ failed_processes):
\*                     /\ FailNode(p)
\*                /\ UNCHANGED <<>>
\*          \/ \* Recover a recovering process, if the RECOVERYRESPONSEs have been received.
\*             \E p \in {p \in 0..NumProcesses-1: processState[p].status = "recovering"}:
\*                /\ Recover(p)
\*                /\ UNCHANGED <<messages>>

\*LatestActiveViewNum == LET
\*                          normal_view_nums == {processState'[p_id].last_active_view_num: p_id \in 0..NumProcesses-1}
\*                       IN
\*                          Maximum(normal_view_nums)
\*
\*\* VRNextExt is VRNext with the extension of updating the ordering variable.
\*VRNextExt == /\ VRNext
\*             /\ \* Set the ordering variable to the ordering as seen at the current leader correponding to the latest active view number.
\*                \* If the leader of this latest view number has failed (i.e., is in "recovering" status), the ordering doesn't change
\*                \* until a new leader is chosen and reaches "normal" status.
\*                \/
\*                    /\ processState'[LatestActiveViewNum % NumProcesses].status # "recovering"
\*                    /\ ordering' = SubSeq(processState'[LatestActiveViewNum % NumProcesses].log,
\*                                        1, processState'[LatestActiveViewNum % NumProcesses].commit_num)
\*                \/
\*                    /\ processState'[LatestActiveViewNum % NumProcesses].status = "recovering"
\*                    /\ ordering' = ordering

\*(* Invariants *)
\*VRTypeOk == /\ processState \in [0..NumProcesses-1 -> [
\*                view_num : 0..MaxViewNum,
\*                commit_num: 0..Cardinality(ClientCommands),
\*                status: {"normal", "view_change", "do_view_change_sent", "recovering"},
\*                last_active_view_num: 0..MaxViewNum,
\*                log: PossibleLogSeqences(ClientCommands),
\*                nonce: 0..MaxFailures]]
\*
\*(* Invariant - for any two processes, log till lesser commit number is the same (Prefix property) *)
\*
\*\* True if sequence a is a prefix of b
\*PrefixOf(a, b) == /\ Len(a) <= Len(b)
\*                  /\ \A i \in 1..Len(a): a[i] = b[i]
\*
\*PrefixLogConsistency == \A a, b \in 0..NumProcesses-1:
\*                            \/ a = b
\*                            \/ PrefixOf(
\*                                SubSeq(processState[a].log, 1, processState[a].commit_num),
\*                                SubSeq(processState[b].log, 1, processState[b].commit_num))
\*                            \/ PrefixOf(
\*                                SubSeq(processState[b].log, 1, processState[b].commit_num),
\*                                SubSeq(processState[a].log, 1, processState[a].commit_num))
\*
\*(* Invariant - process with higher view_num in normal state
\*   has larger log than last committed log of process in lower
\*   view_num *)
\*ViewNumCommitNumInv == \A a, b \in 0..NumProcesses-1:
\*                            \/ a = b
\*                            \/ IF /\ processState[a].status = "normal"
\*                                  /\ processState[b].status = "normal"
\*                                  /\ processState[a].view_num < processState[b].view_num
\*                               THEN processState[a].commit_num <= Len(processState[b].log)
\*                               ELSE TRUE
\*
\*(* Invariant - commit number of other processes <= leader's commit always *)
\*LeaderCommitNumInv == \A a, b \in 0..NumProcesses-1:
\*                            \/ a = b
\*                            \/ IF /\ processState[a].status = "normal"
\*                                  /\ processState[b].status = "normal"
\*                                  /\ processState[a].view_num = processState[b].view_num
\*                                  /\ isLeader(a)
\*                               THEN processState[a].commit_num >= processState[b].commit_num
\*                               ELSE TRUE

\*INSTANCE LinearizableOrdering
\*
\*LnCompliant == LnInit /\ [] [LnNext]_<<ordering>>
=============================================================================
\* Modification History
\* Last modified Mon May 04 10:58:41 CDT 2020 by pkj
\* Created Sat May 02 17:27:40 CDT 2020 by pkj
