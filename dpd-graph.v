Require Colimits.

Add ML Path "/home/rascar/.opam/system/lib/coq/user-contrib/dpdgraph".
Print ML Path.


Declare ML Module "dpdgraph".

Set DependGraph File "colimits.dpd".
Print FileDependGraph

MyTacs
MyLemmas
CommutativeSquares
Diagram
Colimit
Colimit_Prod
Colimit_Sigma
Colimit_trunc

CoEqualizer
Pushout
MappingTelescope

Flattening

IteratedKernelPair.KernelPair_v1
IteratedKernelPair.KernelPair_v2
IteratedKernelPair.IteratedKernelPair
IteratedKernelPair.KPv2_mono
IteratedKernelPair.link_KPv2_CechNerve.

(* Then run 'dpd2dot colimits.dpd'. And open colimits.dot with xdot for instance. *)