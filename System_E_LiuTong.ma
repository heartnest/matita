(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)
include "basics/pts.ma".
include "basics/types.ma".

(*  -----------------------------------------------  *)
(*  Elements of System E *)
(*  -----------------------------------------------  *)

axiom Point : Type[0].
axiom Line : Type[0].
axiom Circle : Type[0].

axiom onl: Point → Line → Prop.
axiom sameside: Point → Point → Line → Prop.
axiom between: Point → Point → Point →  Prop.
axiom onc: Point → Circle → Prop.
axiom inside: Point → Circle → Prop.
axiom center: Point → Circle → Prop.
axiom intersects1: Line → Line → Prop.
axiom intersects2: Line → Circle → Prop.
axiom intersects3: Circle → Circle → Prop.

axiom A: Type[0].
axiom segment: Point → Point → A.
axiom angle: Point → Point → Point → A.
axiom area: Point → Point → Point → A.


(*  -----------------------------------------------  *)
(*  CONSTRUCTION RULES *)
(*  -----------------------------------------------  *)


(* ---- POINTS ---- *)

(* To contruct a poin one has the freedom to choose such 
a point that is distinct from any other elements in the plane*)

(* let a be a point distinct from point b *)
axiom point1:  ∀b.∃a:Point. a≠b.

(* let a be a point on L*)
axiom point2: ∀L.∃a.onl a L.

(* let a be a point on L distinct from point b … *)
axiom point2optPoint: ∀b,L.∃a. a≠b∧onl a L.

(* let a be a point on L between b and c*)
axiom point3: ∀b,c:Point.∀L:Line. b ≠ c → onl b L → onl c L →∃a.onl a L ∧ between b a c.

(* let a be a point on L extending the segment from b to c*)
axiom point4: ∀b,c:Point.∀L:Line. onl b L →  onl c L →b ≠ c→∃a.(onl a L ∧ between a c b).

(* let a be a point on the same side of L as b*)
axiom point5: ∀b:Point.∀L:Line. ¬onl b L → ∃a.sameside a b L.

(* let a be a point on the side of L apposite b*)
axiom point6: ∀b:Point.∀L:Line. ¬onl b L → ∃a.¬onl a L ∧ ¬sameside a b L.

(* let a be a point on alpha*)
axiom point7: ∀alpha,beta:Circle. alpha≠ beta →∃a:Point. onc a alpha.

(* let a be a point inside alpha *)
axiom point8: ∀alpha:Circle. ∃a:Point.inside a alpha.

(* let a be a point outside alpha*)
axiom point9: ∀alpha:Circle. ∃a:Point.¬inside a alpha ∧ ¬onc a alpha.


(* ---- LINES AND CIRCLES ---- *)


(* let L be the line through a and b *)
axiom lc1: ∀a,b:Point. a≠b → ∃L:Line.onl a L ∧onl b L.

(* let alpha be the circle with centre a passing through b*)
axiom lc2: ∀a,b:Point. a ≠ b →∃alpha:Circle. center a alpha ∧ onc b alpha. 


(* ---- INTERSECTIONS ---- *)


(*let a be the intersection of L and M *)
axiom inse1:  ∀L,M:Line. intersects1 L M →  ∃a:Point. onl a L ∧ onl a M.

(* let a be a point of intersection of alpha and L*)
axiom inse2: ∀alpha:Circle. ∀L:Line. intersects2 L alpha →  ∃a:Point. onl a L ∧ onc a alpha.

(*let a and b be the two points of intersection of alpha L*)
axiom inse3: ∀L:Line. ∀alpha:Circle. intersects2 L alpha 
→  ∃a,b:Point. onl a L ∧ onl b L ∧ onc a alpha ∧ onc b alpha ∧ a≠ b.

(*let a be the point of intersection of L and alpha between b and c *)
axiom inse4:∀b,c:Point.∀L:Line.∀alpha:Circle. 
inside b alpha → onl b L → ¬inside c alpha → ¬onc c alpha → onl c L
→ (∃a.onc a alpha ∧ onl a L ∧ between b a c).

(* let a be the point of intersection of L and alpha extending the segment from c to b*)
axiom inse5: ∀b,c:Point.∀L:Line.∀alpha:Circle.
inside b alpha → onl b L → b ≠ c → onl c L 
→ (∃a.onc a alpha ∧onl a L ∧ between a b c).

(* let a be a point on the intersection of alpha and beta*)
axiom inse6:∀alpha,beta:Circle. intersects3 alpha beta 
→ ∃a:Point. onc a alpha ∧ onc a beta.

(* let a and b be the two points of intersection of alpha and beta*)
axiom inse7:∀alpha,beta:Circle. intersects3 alpha beta 
→ ∃a,b:Point. a≠b ∧ onc a alpha ∧ onc a beta ∧onc b alpha ∧ onc b beta.

(* let a be the point of intersection of alpha and beta,on the same side
 of L as b where L is the line through their centers, c and d, respectively.*)
axiom inse8: ∀alpha,beta:Circle.∀L:Line.∀b,c,d:Point. 
intersects3 alpha beta → center c alpha → center d beta
→ onl c L → onl d L → ¬onl b L →(∃a.onc a alpha ∧ onc a beta ∧ sameside a b L).

(* let a be the point of intersection of alpha and beta,
 on the side of L opposite b,where L is the line through their centers, 
 c and d respectively.*)
axiom inse9: ∀alpha,beta:Circle.∀L:Line.∀b,c,d:Point. intersects3 alpha beta → 
center c alpha → center d beta → onl c L → onl d L → ¬onl b L
→ (∃a.onc a alpha ∧ onc a beta ∧ ¬sameside a b L ∧ ¬onl a L).



(*  -----------------------------------------------  *)
(* DIAGRAMMATIC INFERENCES *)
(*  -----------------------------------------------  *)


(* ---- GENERALITIES ---- *)

axiom gen1 : ∀a,b,L,M. a ≠ b → onl a L → onl b L → onl a M → onl b M → L = M.
axiom gen2 : ∀a,b,alpha. center a alpha → center b alpha → a = b.
axiom gen3 : ∀a,alpha. center a alpha → inside a alpha.
axiom gen4 : ∀a,alpha. inside a alpha → ¬onc a alpha.

(* ---- BETWEEN ---- *)

axiom btw1: ∀a,b,c. between a b c → (between c b a ∧ a ≠ b ∧ a ≠ c ∧ ¬between b a c). 
axiom btw2: ∀a,b,c,L.between a b c → onl a L → onl b L → onl c L.
axiom btw3: ∀a,b,c,L. between a b c → onl a L → onl c L → onl b L.
axiom btw4: ∀a,b,c,d. between a b c → between a d b → between a d c.
axiom btw5: ∀a,b,c,d. between a b c → between b c d → between a b d.
axiom btw6: ∀a,b,c:Point. ∀L:Line. a ≠ b →  a≠ c → b≠c → onl a L → onl b L → onl c L 
→ (between a b c ∨ between b a c ∨ between a c b).
axiom btw7: ∀a,b,c,d. between a b c → between a b d → ¬between c b d.

(* ---- SAME SIDE AXIOMS ---- *)

axiom ss1: ∀a,L. ¬onl a L → sameside a a L.
axiom ss2: ∀a,b,L. sameside a b L → sameside b a L.
axiom ss3: ∀a,b,L. sameside a b L → ¬onl a L.
axiom ss4: ∀a,b,c,L. sameside a b L → sameside a c L → sameside b c L.
axiom ss5: ∀a,b,c,L. ¬onl a L → ¬onl b L → ¬onl c L → ¬sameside a b L
 → (sameside a c L ∨ sameside b c L).

(* ---- PASCH AXIOMS ---- *)

axiom psh1: ∀a,b,c,L. between a b c → sameside a c L → sameside a b L.
axiom psh2: ∀a,b,c,L. between a b c → onl a L → ¬onl b L → sameside b c L.
axiom psh3: ∀a,b,c,L. between a b c → onl b L → ¬sameside a c L.
axiom psh4: ∀a,b,c,L,M. L ≠ M → intersects1 L M → onl b L → onl b M 
→ a ≠ c → onl a M → onl c M → a ≠ b → c ≠ b → ¬sameside a c L → between a b c.

(* ---- TRIPLE-INCIDENCE AXIOMS ---- *)

axiom trp1: ∀L,M,N,a,b,c,d. L≠M → L≠N → M≠N → onl a L → onl a M → onl a N →
onl b L → onl c M → onl d N → sameside c d L → sameside b c N → ¬sameside b d M.
axiom trp2: ∀L,M,N,a,b,c,d. L≠M → L≠N → M≠N → onl a L → onl a M → onl a N →
onl b L → onl c M → onl d N → sameside c d L → ¬sameside b d M → ¬onl d M  → b≠a 
→ sameside b c N.
axiom trp3: ∀L,M,N,a,b,c,d,e. L≠M → L≠N → M≠N → onl a L → onl a M → onl a N →
onl b L → onl c M → onl d N → sameside c d L → sameside b c N → sameside d e M 
→ sameside c e N → sameside c e L.

(* ---- CIRCLE AXIOMS ---- *)

axiom cir1: ∀a,b,c,alpha,L. onl a L → onl b L → onl c L 
→ inside a alpha → onc b alpha → onc c alpha → b≠c → between b a c.
axiom cir2: ∀a,b,c,alpha.(inside a alpha ∨ inside b alpha ∨ onc a alpha ∨ onc b alpha)
→ between a c b → inside c alpha.
axiom cir3: ∀a,b,c,alpha. (inside a alpha ∨ onc a alpha) → ¬inside c alpha
→ between a c b → (¬inside b alpha ∧ ¬onc b alpha).
axiom cir4: ∀a,b,c,d,alpha,beta,L. alpha≠beta → intersects3 alpha beta 
→ onc c alpha → onc d alpha → onc c beta → onc d beta → center a alpha → center b beta
→ onl a L → onl b L → ¬sameside c d L.

(* ---- INTERSECTION AXIOMS ---- *)

axiom ins1: ∀a,b,L,M. ¬sameside a b L → ¬onl a L → ¬onl b L → onl a M → onl b M
→ intersects1 L M.
axiom ins2: ∀a,b,L,alpha. (inside a alpha∨onc a alpha)→  (inside b alpha∨onc b alpha)
→ ¬sameside a b L → ¬onl a L → ¬onl b L → intersects2 L alpha.
axiom ins3: ∀a,alpha,L. inside a alpha → onl a L → intersects2 L alpha.
axiom ins4: ∀a,b,alpha,beta. onc a alpha → (onc b alpha ∨ inside b alpha)
→ inside a beta → ¬inside b beta → ¬onc b beta → intersects3 alpha beta.
axiom ins5:∀a,b,alpha,beta. onc a alpha → inside b alpha → inside a beta → onc b beta
→ intersects3 alpha beta.
 

(*  -----------------------------------------------  *)
(* METRIC INFERENCES *)
(*  -----------------------------------------------  *)


axiom plus : A → A →A.
axiom minor: A→ A→Prop. 
axiom O : A.
axiom rightangle : A.

notation "hvbox(a break + b)"
left associative with precedence 44 for @{'plus $a $b}.
interpretation "geometric plus" 'plus x y = (plus x y).

notation "hvbox(a break < b)"
left associative with precedence 47 for @{'less $a $b}.
interpretation "geometric less" 'less x y = (minor x y).

axiom associativity: ∀a,b,c. (a+b)+c = a + (b + c).
axiom commutativity: ∀a,b. a+b = b +a.
axiom identity: ∀a. a+O = a.
axiom minor_trans: ∀a,b,c. a<b → b < c → a < c.
axiom least: ∀a. O < a ∨ O = a.
axiom minor_congruency: ∀a,b,c. a < b → a+c<b+c.

axiom trichotomy: ∀a,b. a < b ∨ b < a ∨ a=b.
axiom irreflex: ∀a. ¬(a<a).
axiom dec_eq_point : ∀a,b:Point. a = b ∨ a ≠ b.


axiom mtr1l: ∀a,b. (a = b → segment a b = O ).
axiom mtr1r: ∀a,b. (segment a b = O → a = b).
axiom mtr2: ∀a,b.  O<segment a b ∨ segment a b = O.
axiom mtr3: ∀a,b. segment a b = segment b a.
axiom mtr4: ∀a,b,c. a≠b →  a≠c → angle a b c = angle c b a.
axiom mtr5: ∀a,b,c. O<angle a b c ∨ angle a b c = O
 ∨ angle a b c  < (rightangle + rightangle)  ∨  rightangle + rightangle = angle a b c.
axiom mtr6: ∀a,b,c.a=b→ area a b c = O.
axiom mtr7: ∀a,b,c.  O < area a b c ∨ area a b c = O.
axiom mtr8: ∀a,b,c. area a b c = area c a b ∧ area a b c = area a c b.
axiom mtr9: ∀a,b,c,a',b',c'. segment a b = segment a' b' 
→ segment b c = segment b' c' → segment c a = segment c' a'
→ angle a b c = angle a' b' c' → angle b c a = angle b' c' a'
→ angle c a b = angle c' a' b' → area a b c = area a' b' c'.


(*  -----------------------------------------------  *)
(* TRANSFER INFERENCES *)
(*  -----------------------------------------------  *)


(* ---- Diagram-segment transfer axioms ---- *)

axiom diaseg1: ∀a,b,c. between a b c →  segment a c = segment a b + segment b c.

axiom diaseg2: ∀a,b,c,alpha,beta. center a alpha → center a beta → onc b alpha
→ onc c beta → segment a b = segment a c → alpha = beta.

axiom diaseg3l: ∀a,b,c,alpha.center a alpha → onc b alpha → (onc c alpha
→ segment a c = segment a b).

axiom diaseg3r: ∀a,b,c,alpha.center a alpha → onc b alpha → 
(segment a c = segment a b → onc c alpha).

axiom diaseg4: ∀a,b,c,alpha. center a alpha → onc b alpha 
→ (inside c alpha →  segment a c < segment a b) ∧ ( segment a c < segment a b → inside c alpha).

axiom diaseg4left: ∀a,b,c,alpha. center a alpha → onc b alpha 
→ inside c alpha → segment a c < segment a b.

axiom diaseg4right: ∀a,b,c,alpha. center a alpha → onc b alpha 
→   segment a c < segment a b  → inside c alpha.


(* ---- Diagram-angle transfer axioms ---- *)


axiom diaang1: ∀a,b,c,L. a≠b → a≠c→ onl a L → onl b L 
→ (onl c L→  ¬between b a c → angle a b c = O) 
∧ (angle a b c = O → (onl c L∧¬between b a c)).

axiom diaang2: ∀a,b,c,d,L,M. onl a L → onl a M → onl b L → onl c M → 
 a≠b→ a≠c→ ¬onl d L → ¬onl d M
 → L≠M→ (angle b a d + angle d a c = angle b a c → sameside b d M ∧ sameside c d L) 
 ∧ ((sameside b d M ∧ sameside c d L) → ((angle b a d) + (angle d a c)= angle b a c)).

axiom diaang3: ∀a,b,c,d,L. onl a L → onl b L → between a c b → ¬onl d L
→ (angle a c d = angle d c b → angle a c d = rightangle)
∧ (angle a c d = rightangle → angle a c d = angle d c b).

axiom diaang4: ∀a,b,c,b',c',L,M. onl a L→ onl b L → onl b' L → onl a M → onl c M
→ onl c' M → a≠b → a≠b' → c≠a → c'≠a → ¬between b a b' → ¬between c a c' 
→ angle b a c = angle b' a c'.

axiom diaang5:∀a,b,c,d,e,L,M,N.onl a L → onl b L→ onl b M → onl c M→ onl c N → onl d N
→ b≠c → sameside a d N →  (angle a b c + angle b c d)< (rightangle + rightangle) 
→ (intersects1 L N) ∧ (onl e L → onl e N → sameside e a M).


(* ---- Diagram-area transfer axioms ---- *)


axiom diaar1: ∀a,b,c,L. onl a L → onl b L → a≠b →
(area a b c = O → onl c L ∧ onl c L → area a b c = O).

axiom diaar1l: ∀a,b,c,L. onl a L → onl b L → a≠b →
area a b c = O → onl c L.

axiom diaar1r: ∀a,b,c,L. onl a L → onl b L → a≠b → onl c L → area a b c = O.

axiom diaar2:∀a,b,c,d,L. onl a L→onl b L→onl c L→a≠b→b≠c→a≠c→ ¬onl d L →
(between a c b → angle a c d + angle d c b = angle a d b)
 ∧ (angle a c d + angle d c b = angle a d b → between a c b).
 
axiom SAS: ∀a,b,c,a',b',c'. 
angle a b c = angle a' b' c' → segment a b = segment a' b'→ segment b c = segment b' c' 
→(segment a c = segment a' c'∧angle a c b= angle a' c' b' ∧ angle c b a = angle c' b' a'). 

axiom SSS: ∀a,b,c,a',b',c'.segment a c = segment a' c'→ segment a b = segment a' b'→ segment b c = segment b' c' 
→(angle c b a = angle c' b' a'∧angle b c a= angle b' c' a' ∧ angle a b c = angle a' b' c'). 




(****************************************)
(****  (* Auxiliary Results *) **********)
(****************************************)


(* Generic a,b,c ...*)

lemma minor_congruency1: ∀a,b,c. a < b → c+a<c+b.
#a #b #c #H1
<commutativity 
>(commutativity c b) @minor_congruency //
qed.

lemma minor_congruency2 : ∀a,b. O < b → a < b + a.
#a #b #H1 <(identity a) in ⊢ (?%?); <commutativity 
>(commutativity a b) @minor_congruency //
qed.

lemma eqc_intrm : ∀a,b. a <b → a = b → False.
#a #b #H1 #H2 @(absurd ? H1) >H2 @irreflex 
qed.

lemma eq_congruency : ∀a,b,c. a + b = a + c → b = c.
#a #b #c #H1 cases (trichotomy b c) 
[ * [ #H2 @False_ind @(eqc_intrm … H1) @minor_congruency1 // 
    | #H3 @False_ind @(eqc_intrm … (sym_eq … H1)) @minor_congruency1 //]
| // 
] 
qed.

(* Segments ...*)

lemma seg_existance_pre: ∀a,b. a≠b→  segment a b ≠O.
#a #b #ab % #H1 @(absurd ? ? ab)  @(mtr1r) //  
qed.

lemma seg_existance_pre_inv: ∀a,b. segment a b ≠O → a≠b.
#a #b #ab % #H1 @(absurd ? ? ab) @(mtr1l) //  
qed.

lemma seg_existance: ∀a,b. a≠b →  O < segment a b.
#a #b #ab 
lapply (seg_existance_pre a b ab) #H1  
cases(mtr2 a b) [ // | #H2 @False_ind @(absurd ? H2 H1) 
qed.

lemma seg_additivity: ∀a,b. O < segment a b 
→  segment a b < segment a b + segment a b.
#a #b #H1 @minor_congruency2 // 
qed.

lemma seg_congruency: ∀a,b,c,d,e,f:Point. 
segment a b + segment c d = segment a b + segment e f
→ segment c d = segment e f.
#a #b #c #d #e #f #H1 @eq_congruency //
qed.

(* Points ...*)

lemma not_same_line_means_diff: ∀a,b,L. onl a L→ ¬onl b L → a≠b.
#a #b #L #H1 #H2 % #eq_ab @(absurd ? H1 ?) >eq_ab //
qed.

lemma diff_point1: ∀a,b,alpha. center a alpha → onc b alpha → a ≠b.
#a #b #alpha #H1 #H2 
lapply(gen3 … H1) #H3 
lapply(gen4 … H3) #H4 
% #H5 @(absurd ? H2 ?) <H5 // 
qed.

lemma diff_point2: ∀a,b,c,L,M. L≠M→ 
onl a L → onl b L→ onl b M → onl c M → b≠c → b≠a → a ≠c.
#a #b #c #L #M #H1 #H2 #H3 #H4 #H5 #H6 #H7  
% #H8
elim H1 #H9 @H9 
lapply(gen1 b c L M H6 H3 ? H4 H5) <H8 // 
qed.

lemma side1: ∀a,b,L. ¬sameside a b L → ¬onl a L → ¬onl b L → a≠b.
#a #b #L #H1 #H2 #H3 
% #eq_ab @(absurd ? ? H1) <eq_ab
@ss1 //
qed.

lemma not_onL: ∀a,b,c,L,M,N.
b≠c→b≠a→M≠N→onl b M→onl b N→onl a M→onl c N→onl a L→onl c L
→¬onl b L.
#a #b #c #L #M #N #H1 #H2 #H3 #H4 #H5 #H6 #H7 #H8 #H9
 % #H10 
@(absurd (M=N) ? H3) (* /3 width=9 by trans_eq, gen1/ *)
@(trans_eq ?? L) (* /2 by gen1/ *)
  [@(gen1 b a ?? H2 H4 H6 H10 H8)
  |@(gen1 b c ?? H1 H10 H9 H5 H7)
  ]
qed.

lemma eq_segbtw: ∀a,b,c,L. onl a L→ onl b L→ onl c L→ a≠c→ 
segment a b = segment b c → between a b c.
 #a #b #c #L #on_aL #on_bL #on_cL #neqac #eqabbc
 cases (dec_eq_point a b)
   [#H @False_ind >(mtr1l  … H) in eqabbc; #H1
    lapply (mtr1r … (sym_eq … H1)) #H2 @(absurd ?? neqac) //
   |#neqab cases (dec_eq_point b c)
     [#H @False_ind >(mtr1l  … H) in eqabbc; #H1
      lapply (mtr1r … H1) #H2 @(absurd ?? neqac) //
     |#neqbc 
     lapply (btw6 a b c L neqab neqac neqbc on_aL on_bL on_cL) 
      * [*
          [//
           |#H @False_ind 
           lapply (diaseg1 … H) <eqabbc >(mtr3 b a) 
           >commutativity #H1
           @(absurd (segment a b < segment a b) ? (irreflex ?))
           >H1 in ⊢ (* \vdash *) (??%); @minor_congruency2 
            @seg_existance //
           ] 
        ]
        #H' @False_ind 
        lapply(diaseg1 … H') >(mtr3 c b) <eqabbc
         #H1
        @(absurd (segment a b < segment a b) ? (irreflex ?))
        >H1 in ⊢(??%); @minor_congruency2 @seg_existance 
      ]
    ]//
qed. 
        
lemma zeronum:∀a. a+a=O → a=O.
#a #H cases(least a)  
[ 
  | //
]  #H1
lapply(minor_congruency2 a a H1) >H #H2 
@False_ind 
lapply(minor_trans a O a H2 H1) #H3
@(absurd ? H3 ?) 
lapply(irreflex a) // 
qed.

lemma zeroseg: ∀a,b. segment a b + segment a b = O→ segment a b = O.
#a #b #H @zeronum // 
qed.

lemma bwt_more1: ∀a,b. a≠b →  ¬between a b a.
#a #b  #H1 % #H2
lapply(mtr1l a a ?) [//] #H3
lapply (diaseg1 a b a H2) >H3 #H4
lapply (zeroseg a b ?) [//] #H5
@(absurd (a=b) ? H1) @mtr1r //
qed.

lemma bwt_more2:∀a,b,c,L. onl b L→ ¬onl c L
→ ¬sameside a c L → ¬between a c b.
#a #b #c #L  #H1  #H3 #H4  
% #H8  elim H4 #H9 @H9 
lapply (psh2 b c a L ? H1 H3) [ | @ss2] 
lapply (btw1 a c b H8) * * * #H10 #H11 #H12 #H13 // 
qed.

lemma crt_distinct_line: ∀a,b,c,L. onl a L→onl b L→ ¬onl c L→
∃K. onl a K∧onl c K∧K≠L.
#a #b #c #L #on_al #on_bl #non_cl
lapply(lc1 a c ?) [ % #eq_ac @(absurd ? ? non_cl) <eq_ac // ]
* #K * #on_ak #on_ck
@(ex_intro … K)
% [ 
    /2/
    | % #kl @(absurd ? ? non_cl) <kl // 
  ]
qed.


(****************************************)
(****  (* Euclide Propositions *)  ******)
(****************************************)


lemma propositionI1 : ∀a,b:Point. a ≠ b 
→ ∃c:Point. (segment a b = segment b c ∧ segment b c = segment c a).
#a #b #neqab
lapply (lc2 a b neqab) * #alpha * #center_a_alpha #on_b_alpha 
lapply (lc2 b a ?) [/2/] * #beta * #center_b_beta #on_a_beta 
lapply (ins5 b a alpha beta on_b_alpha ? ? on_a_beta)
[ lapply (gen3 a alpha) /2/ ] 
[lapply (gen3 b beta) /2/ ] #intersection
lapply (inse6 alpha beta intersection) * #c * #on_c_alpha #on_c_beta
lapply (diaseg3l a b c alpha center_a_alpha on_b_alpha on_c_alpha)
#segacab
lapply (diaseg3l b a c beta center_b_beta on_a_beta on_c_beta)
#segbaba
@(ex_intro … c) % // 
qed.


lemma propositionI1_var : ∀a,b,d,L.a≠b→onl a L→onl b L→¬onl d L  
→ ∃c.¬sameside c d L ∧¬onl c L ∧(segment a b = segment b c ∧ segment b c = segment c a).
#a #b #d #L #neqab #H1 #H2 #H3
lapply (lc2 a b neqab) * #alpha * #center_a_alpha #on_b_alpha 
lapply (lc2 b a ?) [/2/] * #beta * #center_b_beta #on_a_beta
lapply (ins5 b a alpha beta on_b_alpha ? ? on_a_beta)
[ lapply (gen3 a alpha) /2/ ] 
[lapply (gen3 b beta) /2/ ] #intersection
lapply (inse9 alpha beta L d a b intersection center_a_alpha center_b_beta H1 H2 H3)
* #c * * * #on_c_alpha #on_c_beta #H6 #H7
lapply(side1 c d L H6 H7 H3) #H8
lapply (diaseg3l a b c alpha center_a_alpha on_b_alpha on_c_alpha)
#segacab
lapply (diaseg3l b a c beta center_b_beta on_a_beta on_c_beta)
#segbaba
lapply (diaseg3l a b c alpha center_a_alpha on_b_alpha on_c_alpha)
#segacab
lapply (diaseg3l b a c beta center_b_beta on_a_beta on_c_beta)
#segbaba
@(ex_intro … c) %  /2/ 
qed.


lemma propositionI1_auxiliary1: ∀a,b,c:Point. a ≠ b 
→ segment a b = segment b c → segment b c = segment c a → c≠a ∧ c≠b.
#a #b #c #neq_ab #segabbc #segbcca 
lapply(seg_existance_pre a b neq_ab) #segabO 
% @seg_existance_pre_inv // 
qed.


lemma propositionI1_auxiliary2: ∀a,b,c,L. a≠b-> onl a L → onl b L 
→ segment a b = segment b c → segment b c = segment c a → ¬onl c L.
#a #b #c #L #neq_a_b #onl_a_L #onl_b_L #segmentabbc #segmentbcca
lapply(propositionI1_auxiliary1 a b c neq_a_b segmentabbc segmentbcca)
* #H2 #H3
% #H1 lapply(btw6 a b c L neq_a_b ? ? onl_a_L onl_b_L H1) /2/
* [ * 
    [ #H lapply(diaseg1 … H) <(mtr3 c a)
    >segmentabbc >segmentbcca
    #H5 @(absurd (segment c a < segment c a) ? (irreflex ?))
         >H5 in ⊢ (* \vdash *) (??%); @minor_congruency2 
        @seg_existance //
    ] #H lapply(diaseg1 … H) <(mtr3 c a) <(mtr3 a b)
    >segmentabbc <segmentbcca #H5
    @(absurd (segment b c < segment b c) ? (irreflex ?))
    >H5 in ⊢ (* \vdash *) (??%); @minor_congruency2 
        @seg_existance @sym_not_eq //
      ] 
      #H lapply(diaseg1 … H) <(mtr3 c a) <(mtr3 b c)
    >segmentabbc <segmentbcca #H5
    @(absurd (segment b c < segment b c) ? (irreflex ?))
    >H5 in ⊢ (* \vdash *) (??%); @minor_congruency2 
        @seg_existance @sym_not_eq //
qed.


lemma propositionI2: ∀a,b,c,L.b≠c→onl b L→onl c L→a≠b→a≠c
→ ∃f. segment a f = segment b c.
#a #b #c #L #H1 #H2 #H3 #H4 #H5 
lapply (propositionI1 a b H4) * #d * #H6 #H7
lapply(seg_existance_pre a b H4) #segab_notO
lapply(seg_existance_pre_inv b d ?) // #not_eq_bd
lapply(seg_existance_pre_inv d a ?) // #not_eq_da
lapply (lc1 d a not_eq_da) * #M * #H8 #H9
lapply (lc1 d b (sym_not_eq … not_eq_bd)) * #N * #H10 #H11
lapply (lc2 b c H1) * #alpha * #H12 #H13 
lapply (inse5 b d N alpha ? H11 not_eq_bd H10) [@gen3 //] 
* #g * * #H14 #H15 #H16 
lapply (diaseg1 d b g ?) 
lapply (btw1 g b d H16) 
* * * // #H17 #H18 #H19 #H20 #H21 >H7
lapply (lc2 d g (sym_not_eq … H19))  * #beta * #H22 #H23   
lapply (diaseg4right d g a beta H22 H23 ?) 
>H21 lapply (mtr3 d b) #H24 >H24 >H7
lapply (seg_existance g b H18) #H25 
lapply (minor_congruency2 (segment d a) (segment g b) H25)  #H26 // #H27
lapply (inse5 a d M beta H27 H9 ? H8) [@seg_existance_pre_inv //] 
* #f * * #H28 #H29 #H30
lapply (diaseg1 d a f ?) 
lapply (btw1 f a d H30) * * * #H31 #H32 #H33 #H34 // #H35
lapply (diaseg3l d g f beta H22 H23 H28) >H35 >H21
lapply (mtr3 d b) #H36 >H36 >H7 #H37
lapply (diaseg3l b g c alpha H12 H14 H13) #H37
lapply (seg_congruency d a a f b g ?) // #H38
@(ex_intro … f) // 
qed. 

          
lemma propositionI9: ∀a,M,N. M≠N→ onl a M → onl a N 
→ ∃e,b,c. onl b M ∧ onl c N ∧  angle b a e = angle c a e. 
#a #M #N #H0 #H1 #H2
lapply (point2optPoint a M) * #b * #H3 #H4
lapply(lc2 a b (sym_not_eq … H3))  * #alpha * #H7 #H8
lapply(gen3 … H7) #inside_a_alpha
lapply(ins3 … inside_a_alpha H2) #intersect_Nalpha
lapply(inse2 alpha N intersect_Nalpha) 
 * #c * #H9 #H10
lapply (diff_point1 a c alpha H7 H10) #H11
lapply(diaseg3l a b c alpha H7 H8 H10) #H12  
lapply(diff_point2 b a c M N H0 H4 H1 H2 H9 H11 (sym_not_eq … H3)) #H13
lapply(lc1 b c H13) * #L * #H14 #H15
lapply(not_onL b a c L M N H11 (sym_not_eq … H3) H0 H1 H2 H4 H9 H14 H15) 
#H16
lapply(propositionI1_var b c a L H13 H14 H15 H16)
* #e * * #H17 #H18 * #H19 #H20
lapply(diff_point2 b a c M N H0 H4 H1 H2 H9 H11 (sym_not_eq … H3)) 
#neq_bc 
lapply(SSS e b a e c a ? ? ?) // * * #ang1 #ang2 #ang3 
@(ex_intro … e) @(ex_intro … b) @(ex_intro … c)
% [ % //] //
qed.  



lemma propositionI10:∀a,b,L. a≠b→ onl a L→ onl b L
→∃d. between a d b∧segment a d=segment d b.
#a #b #L #H1 #H2 #H3
lapply(propositionI1 a b H1) * #c * #H4 #H5
lapply(propositionI1_auxiliary1 a b c H1 H4 H5)
* #H6 #H7 
lapply(lc1 c a ?) // * #M * #H8 #H9
lapply(propositionI1_auxiliary2 c a b M H6 H8 H9 ? H4) 
// #not_onl_bm 
lapply(crt_distinct_line c a b M H8 H9 not_onl_bm ) 
* #N * *  #H10 #H11 #H12
lapply(not_onL a c b L M N H7 H6 (sym_not_eq … H12) H8 H10 H9 H11 H2 H3)
#H13
lapply(propositionI1_var a b c L H1 H2 H3 H13) 
* #e * * #H14 #H15 * #H16 #H17 
lapply(SSS e a c e b c ? ? ?) // * * #H18  #H19 #H20
lapply(side1 … H14 H15 H13) #neq_ec
lapply(lc1 c e (sym_not_eq … neq_ec)) 
* #K * #H20 #H21
lapply(ins1 e c L K H14 H15 H13 H21 H20) #H22 
lapply(inse1 L K H22) * #d * #H23 #H24
lapply(not_same_line_means_diff d c L H23 H13) #neq_dc
lapply(bwt_more1 a c (sym_not_eq …H6)) #not_btwac
lapply(bwt_more1 b c (sym_not_eq …H7)) #not_btwbc
lapply(bwt_more2 e d c L H23 H13 H14) #H25
lapply (diaang4 c a e a d M K H8 H9 H9 H20 H21 H24
 H6 H6 neq_ec neq_dc not_btwac H25)
#H26
lapply (diaang4 c b e b d N K H10 H11 H11 H20 H21 H24 H7 H7 neq_ec neq_dc not_btwbc H25)
#H27
lapply(SAS a c d b c d ? ? ?) 
//  * * #H28 #H29 #H30
@(ex_intro … d) % 
[
  @(eq_segbtw a d b L H2 H23 H3 H1 ?) //
  | //
] 
qed.

  