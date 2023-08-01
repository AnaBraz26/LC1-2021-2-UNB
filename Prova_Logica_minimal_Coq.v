Parameter phi1 phi2: Prop.

Section regra1.
Hypothesis H1: phi1.
Hypothesis H2: phi2.

Lemma Introducao_da_conjuncao: phi1 /\ phi2.
Proof.
  split.
  assumption.
  assumption.
Qed.
End regra1.

Section regra2.
Hypothesis H: phi1 /\ phi2.

Lemma Eliminacao_da_conjuncao_esquerda: phi1.
Proof.
  destruct H.
  assumption.
Qed.
End regra2.

Section regra2'.
Hypothesis H: phi1 /\ phi2.

Lemma Eliminacao_da_conjuncao_direita: phi2.
Proof.
 destruct H.
 assumption.
Qed.
End regra2'.

Section regra3.
Hypothesis H: phi1.

Lemma Introducao_disjuncao_esquerda: phi1 \/ phi2.
Proof.
 left. 
 assumption.
Qed.
End regra3.

Section regra3'.
Hypothesis H: phi2.

Lemma Introducao_disjuncao_direita: phi1 \/ phi2.
Proof.
  right.
  assumption.
Qed.
End regra3'.

Section regra4.
   Variable gamma: Prop.  
Hypothesis H: phi1 \/ phi2.
Hypothesis H1: phi1 -> gamma.
Hypothesis H2: phi2 -> gamma.
  
Lemma Eliminacao_disjuncao: gamma.
Proof.
   destruct H.
   apply H1 in H0.
   assumption.
   apply H2 in H0.
   assumption.
Qed.
End regra4.

Section regra5.
Hypothesis H1: phi1 -> phi2.

Lemma Introdução_da_implicacao: phi1 -> phi2.
Proof.
  intro.
  apply H1 in H.
  assumption.
Qed.
End regra5.

Section regra6.
Hypothesis H1: phi1.
Hypothesis H2: phi1 -> phi2.

Lemma Modus_ponens: phi2.
Proof.
  apply H2 in H1.
  assumption.
Qed.
End regra6.

Section regra7.
Hypothesis H1: phi1 -> phi2.
Hypothesis H2: ~phi2.

Lemma Introducao_negacao: ~phi1.
Proof.
  intro.
  apply H1 in H.
  apply H2 in H.
  assumption.
Qed.
End regra7.

Section regra8.
Hypothesis H1: phi1.
Hypothesis H2: ~phi1.

Lemma Absurdo: False.
Proof.
 apply H2.
 assumption.
Qed.
End regra8.








