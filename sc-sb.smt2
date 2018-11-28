;------------------------------
; MCM: Sequential Consistency
; MCM constraints for program 
; 
;  [x] = 0 and [y] = 0
;  T1:          | T2:  
;    st [x],1   |     st [y],1
;    ld r1, [y] |     ld r2, [x]
;
;   P: r1 = 0 and r2 = 0
;-----------------------------

(set-option :produce-models true)

; Variable definitions - SSA variables
(declare-fun v_x_0     () (_ BitVec 8))
(declare-fun v_y_0     () (_ BitVec 8))
(declare-fun v_x_T1_1  () (_ BitVec 8))
(declare-fun v_y_T2_1  () (_ BitVec 8))
(declare-fun v_r2_T2_1 () (_ BitVec 8))
(declare-fun v_r1_T1_1 () (_ BitVec 8))

; Variable definitions for Pi-functions
(declare-fun pi_x_T2_1 () (_ BitVec 8))
(declare-fun pi_y_T1_1 () (_ BitVec 8))

; Variable definitions - Timestamps
(declare-fun t1 () Int)
(declare-fun t2 () Int)
(declare-fun t3 () Int)
(declare-fun t4 () Int)

; State update constraints
(assert (= v_x_0    #x00))
(assert (= v_y_0    #x00))
(assert (= v_x_T1_1 #x01))
(assert (= v_y_T2_1 #x01))
(assert (= v_r2_T2_1 pi_x_T2_1))
(assert (= v_r1_T1_1 pi_y_T1_1))

; Pi-functions
(assert (or (and (= pi_y_T1_1 v_y_T2_1) (< t3 t2) (or (> t3 0) (< t2 0)))
            (and (= pi_y_T1_1 v_y_0)    (> t2 0)  (or (< t3 0) (> t3 t2)))))
(assert (or (and (= pi_x_T2_1 v_x_T1_1) (< t1 t4) (or (> t1 0) (< t4 0)))
            (and (= pi_x_T2_1 v_x_0)    (> t4 0)  (or (< t1 0) (> t1 t4)))))

; Program order
(assert (> t1 0))
(assert (< t1 t2))
(assert (> t3 0))
(assert (< t3 t4))

; Property
(assert (and (= v_r1_T1_1 #x00) (= v_r2_T2_1 #x00)))

; Check
(check-sat)

; Model
; (get-model) ; will be unsat, so no model is available