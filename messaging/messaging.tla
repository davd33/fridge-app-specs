----------------------------- MODULE messaging -----------------------------

EXTENDS Naturals, PT, FiniteSets

(***************************************************************************)
(* The messaging in the fridjapp needs to ensure a coherence in the data.  *)
(* This is achieved with version numbers and sending of messages between   *)
(* devices.  Here we specify the synchronization of one fridj across       *)
(* various instances hosted by different devices, one being the lead (the  *)
(* creator of the shared fridj).                                           *)
(***************************************************************************)

CONSTANTS DEVICES, \* contains synchronizing devices 
          DATA,    \* all possible data values
          LEAD     \* the creator of the fridj has precedence

ASSUME LEAD \in DEVICES

VARIABLES fridjs, msgs, network

vars == <<fridjs, msgs, network>>

(***************************************************************************)
(* The fridj's data is represented by some element in the set DATA.        *)
(***************************************************************************)
FridjValue == [v: Nat,  \* version
               d: DATA] \* some data (could be an ingredient item)
               
Fridj == [DEVICES -> FridjValue] 

FridjInv == fridjs \in Fridj

(***************************************************************************)
(* All messages ever sent are added to the msgs.  Messages not yet sent    *)
(* can be modified by the sending device.                                  *)
(***************************************************************************)
Msg == [to: DEVICES, \* device receiving the message
        from: DEVICES,
        sent: BOOLEAN, \* true iff to and from are in the network
        type: {"synch", "conn"}, \* either a connection or synch
        data: FridjValue]

MsgInv == msgs \subseteq Msg

(***************************************************************************)
(* The network contains the list of connected devices.                     *)
(***************************************************************************)
Network == SUBSET DEVICES

NetworkInv == network \in Network

(***************************************************************************)
(* First version of a fridj is any Natural number.                         *)
(***************************************************************************)
FirstVersion == \E n: n \in Nat

(***************************************************************************)
(* Compute the maximum version of the fridj by looking at each instance's  *)
(* version.                                                                *)
(***************************************************************************)
LattestVersion == ReduceSet(
    LAMBDA d, v: Max(fridjs[d].v, v),
    DEVICES, FirstVersion)

(***************************************************************************)
(* What a synch version and data value means: nothing.                     *)
(***************************************************************************)
AnyVersion == FirstVersion
AnyData == CHOOSE d \in DATA: TRUE

-----------------------------------------------------------------------------
(***************************************************************************)
(* Following definitions are state functions and actions taken by the user *)
(* or that represent the management of a transaction across devices.       *)
(***************************************************************************)

(***************************************************************************)
(* Device's conn messages have been sent                                   *)
(***************************************************************************)
AllConnMsgsSent(device) ==
    ~ \E msg \in msgs: /\ msg.type = "conn"
                       /\ msg.sent
                       /\ msg.from = device 

(***************************************************************************)
(* All received conn messages have been read.                              *)
(***************************************************************************)
AllConnMsgsRead(device) ==
    ~ \E msg \in msgs: /\ msg.type = "conn"
                       /\ msg.sent
                       /\ msg.to = device 

(***************************************************************************)
(* All received synch messages have been read.                             *)
(***************************************************************************)
AllSynchMsgsRead(device) ==
    ~ \E msg \in msgs: /\ msg.type = "synch"
                       /\ msg.sent
                       /\ msg.to = device

(***************************************************************************)
(* Send a message to notify the other devices of a state change.           *)
(***************************************************************************)
Notify(devices, version, data, sender) ==
    /\ msgs' = msgs \union {[to |-> d, 
                             from |-> sender,
                             sent |-> /\ d \in network
                                      /\ sender \in network,
                             type |-> "synch",
                             data |-> [v |-> version, d |-> data]]: d \in devices}

(***************************************************************************)
(* Send messages not yet sent through network.                             *)
(***************************************************************************)
SendAll(device) ==
    /\ device \in network
    /\ msgs' = {m \in msgs: m.from /= device \/ m.sent = TRUE} \union
               {[dm EXCEPT !.sent = dm.to \in network]: 
                    dm \in {m \in msgs: m.from = device /\ m.data.v >= fridjs[device].v}}
    /\ UNCHANGED <<fridjs, network>>

(***************************************************************************)
(* It's required to read messages to update the data to a new version.     *)
(***************************************************************************)
ReadSynchMsg(device) == \E msg \in {m \in msgs: m.type = "synch"}:
    /\ msg.to = device
    /\ msg.sent
    /\ msg.data.v >= fridjs[device].v
    /\ fridjs' = [fridjs EXCEPT ![device] = msg.data]
    /\ msgs' = msgs \ {msg}
    /\ UNCHANGED network

(***************************************************************************)
(* When a device connects to the network, it sends a notification to the   *)
(* connected devices.  So we need to read these messages too.  There are   *)
(* two cases:                                                              *)
(*     - the sent version is newer so we update on our side                *)
(*     - the sent version is older and we send an update                   *)
(***************************************************************************)
ReadConnMsg(device) == \E msg \in {m \in msgs: m.type = "conn"}:
    /\ msg.to = device
    /\ msg.sent
    /\ AllSynchMsgsRead(device)
    /\ IF msg.data.v >= fridjs[device].v
       THEN /\ fridjs' = [fridjs EXCEPT ![device] = msg.data]
            /\ msgs' = msgs \ {msg}
       ELSE /\ LET msg_sent == device \in network /\ msg.from \in network
                   new_msg == [to |-> msg.from,
                               from |-> device,
                               sent |-> msg_sent,
                               type |-> "synch",
                               data |-> fridjs[device]]
               IN msgs' = (msgs \ {msg, [new_msg EXCEPT !.sent = FALSE]}) 
                          \union {new_msg}
            /\ UNCHANGED fridjs
    /\ UNCHANGED network

(***************************************************************************)
(* Update the fridj after the user's input.  Here implemented by a simple  *)
(* increment of the counter.                                               *)
(***************************************************************************)
FridjUserInput(device) == \E dt \in DATA:
    LET new_version == fridjs[device].v + 1
    IN
        \* no synch to do or new connections to handle
        /\ ~ \E msg \in msgs: msg.to = device /\ msg.sent
        \* wait for synch on device's connection
        /\ AllConnMsgsSent(device)
        /\ LEAD \in network /\ device \in network
        /\ fridjs' = [fridjs EXCEPT ![device] = [d |-> dt,
                                                 v |-> new_version]]
        /\ Notify({d \in DEVICES: d /= device}, 
                   new_version, 
                   dt, 
                   device)
        /\ UNCHANGED network

(***************************************************************************)
(* Devices must connect to the network to be able to share messages.       *)
(***************************************************************************)
Connect(device) == 
    /\ device \notin network
    /\ network' = network \union {device}
    /\ AllSynchMsgsRead(device)
    /\ AllConnMsgsRead(device)
    \* send msg to other connected devices
    /\ msgs' = msgs \union {[to |-> d, 
                             from |-> device,
                             sent |-> d \in network,
                             type |-> "conn",
                             data |-> fridjs[device]]: d \in network}
    /\ UNCHANGED <<fridjs>>


(***************************************************************************)
(* Every device can loose its internet connection at some point.           *)
(***************************************************************************)
Disconnect(device) ==
    /\ device \in network
    /\ AllConnMsgsRead(device)
    /\ network' = network \ {device}
    /\ UNCHANGED <<msgs, fridjs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Temporal formula definition of the specification.                       *)
(***************************************************************************)
Init == \E dt \in DATA:
    /\ fridjs = [d \in DEVICES |-> [v |-> FirstVersion,
                                    d |-> dt]]
    /\ msgs = {}
    /\ network = {}

Next == \E d \in DEVICES: 
    \/ FridjUserInput(d)
    \/ ReadSynchMsg(d)
    \/ ReadConnMsg(d)
    \/ Connect(d)
    \/ Disconnect(d)
    \/ SendAll(d)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariant: For every fridj instance, version equality implies data      *)
(* equality.                                                               *)
(***************************************************************************)
SynchronizedFridjs == \A d1, d2 \in DEVICES: 
    fridjs[d1].v = fridjs[d2].v => fridjs[d1].d = fridjs[d2].d

(***************************************************************************)
(* Associated theorems for previously defined type and safety invariants.  *)
(***************************************************************************)
THEOREM Spec => /\ []FridjInv
                /\ []MsgInv
                /\ []NetworkInv
                /\ []SynchronizedFridjs

=============================================================================
\* Modification History
\* Last modified Sun Oct 27 01:09:52 CEST 2024 by davd33
\* Created Sat Oct 26 14:17:55 CEST 2024 by davd33
