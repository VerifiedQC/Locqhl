(** * QuantumActions — meaning of the quantum primitives U, M, and init.

      U[q̄]      :  ρ ↦ U ρ U†
      q := |0>  :  ρ ↦ |0>_q<0| ρ |0>_q<0| + |0>_q<1| ρ |1>_q<0|
      x := M[q̄] :  outcome m ∈ T_M gives (σ[x↦m], M_m ρ M_m†). 
** *)

From QuantumLib Require Import Matrix Quantum Pad.
From Locqhl.Core Require Import Syntax.

Local Open Scope matrix_scope.

(** ** State carrier
    The global quantum state is a density matrix over [dim] qubits.  
    Quantum.v:1723: Notation Density n := (Matrix n n)
** **)
Definition qstate (dim : nat) : Type := Density (2 ^ dim).

(** ** Unitary evolution:  ρ ↦ U ρ U† ** **)
(*** Quantum.v:1928:
Definition super {m n} (M : Matrix m n) : Superoperator n m :=
fun ρ => M × ρ × M†. 

Matrix.v:54:
Notation Square n := (Matrix n n). 
***)
Definition apply_unitary {dim} (U : Square (2 ^ dim)) : qstate dim -> qstate dim :=
  super U.

(** ** Initialization:  q := |0> ** **)
(*** Set qth qubit to |0> 
pad_u dim q ∣0⟩⟨0∣  =  I ⊗ … ⊗ ∣0⟩⟨0∣ ⊗ … ⊗ I 
***)
Definition apply_init {dim} (q : qvar) : qstate dim -> qstate dim :=
  fun ρ => super (pad_u dim q (∣0⟩⟨0∣)) ρ .+ super (pad_u dim q (∣0⟩⟨1∣)) ρ.

(** ** Measurement
    pair:  
    fst = T_M (the finite outcome set),  
    snd = {M_m} (outcome ↦ operator). 
** **)
Definition measurement (dim : nat) : Type :=
  list nat * (nat -> Square (2 ^ dim)).

Definition apply_meas {dim} (M : measurement dim) (m : nat) : qstate dim -> qstate dim :=
  super (snd M m).
