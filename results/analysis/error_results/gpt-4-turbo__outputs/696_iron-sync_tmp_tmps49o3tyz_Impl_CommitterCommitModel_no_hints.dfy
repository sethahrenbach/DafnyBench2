
// include "IOModel.i.dfy"
// include "../lib/DataStructures/LinearMutableMap.i.dfy"

module CommitterCommitModel {
  import opened NativeTypes
  import opened Options

  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened ViewOp
  import JC = JournalCache
  import opened Journal
  import opened JournalBytes
  import opened DiskOpModel
  import SectorType

  import LinearMutableMap
  import opened IOModel

  predicate Inv(m: LinearHashMap<JC.SyncReqStatus>)
  predicate WFIter(m: LinearHashMap<JC.SyncReqStatus>, it: Iterator<JC.SyncReqStatus>)
  function IterStart(m: LinearHashMap<JC.SyncReqStatus>): Iterator<JC.SyncReqStatus>
  function IterInc(m: LinearHashMap<JC.SyncReqStatus>, it: Iterator<JC.SyncReqStatus>): Iterator<JC.SyncReqStatus>
  function Insert(m: LinearHashMap<JC.SyncReqStatus>, key: int, value: JC.SyncReqStatus): LinearHashMap<JC.SyncReqStatus>

  function SyncReqs2to1Iterate(
      m: LinearHashMap<JC.SyncReqStatus>,
      it: Iterator<JC.SyncReqStatus>,
      m0: LinearHashMap<JC.SyncReqStatus>)
    : (m' : LinearHashMap<JC.SyncReqStatus>)
  requires Inv(m)
  requires WFIter(m, it)
  requires Inv(m0)
  requires m0.Keys == it.s // Assuming 's' is a valid field representing the set of keys seen so far
  ensures Inv(m')
  decreases it.decreaser // Assuming 'decreaser' is a valid field to support termination checking
  {
    if it.next.Done? then
      m0
    else {
      SyncReqs2to1Iterate(
        m,
        IterInc(m, it),
        Insert(m0, it.next.key, (if it.next.value == State2 then State1 else it.next.value))
      )
    }
  }

  function {:opaque} SyncReqs2to1(m: LinearHashMap<JC.SyncReqStatus>)
      : (m' : LinearHashMap<JC.SyncReqStatus>)
  requires Inv(m)
  ensures Inv(m')
  {
    var m0 := new LinearHashMap<JC.SyncReqStatus>; // Instantiation moved to a separate statement
    SyncReqs2to1Iterate(m, IterStart(m), m0)
    return m0; // Return the modified map
  }
}
