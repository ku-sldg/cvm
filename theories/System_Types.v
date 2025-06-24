From RocqCandy Require Import All.

Definition FS_Location := string.
Opaque FS_Location.
Global Instance Stringifiable_FS_Location : Stringifiable FS_Location.
typeclasses_eauto.
Defined.
Global Instance DecEq_FS_Location : DecEq FS_Location.
typeclasses_eauto.
Defined.

Definition IP_Port := string.
Opaque IP_Port.
Global Instance Stringifiable_IP_Port : Stringifiable IP_Port.
typeclasses_eauto.
Defined.
Global Instance DecEq_IP_Port : DecEq IP_Port.
typeclasses_eauto.
Defined.

Definition Public_Key := string.
Opaque Public_Key.
Global Instance Stringifiable_Public_Key : Stringifiable Public_Key.
typeclasses_eauto.
Defined.
Global Instance DecEq_Public_Key : DecEq Public_Key.
typeclasses_eauto.
Defined.