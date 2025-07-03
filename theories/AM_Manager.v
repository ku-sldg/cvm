From RocqCandy Require Import All.
From RocqJSON Require Import JSON.
From CoplandSpec Require Import System_Types.
From CoplandManifestTools Require Import Manifest.

Record AM_Manager_Config := 
  mkAM_Man_Conf {
  am_manager_manifest   : Manifest ;
  am_manager_asp_bin    : FS_Location ;
  (* am_manager_ipport       : IP_Port ; *)
}.

Record AM_Manager_St := 
  mkAM_Manager_St {
    am_manager_config : AM_Manager_Config;
  }.

Definition AM_Manager A := (Result (A * AM_Manager_St) string).
