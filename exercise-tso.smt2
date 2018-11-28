;------------------------------
; MCM: Total Store Order
; MCM constraints for program 
; 
;  [x] = 0 and [y] = 0
;  T1:          | T2:  
;    st [x],1   |   ld r1, [y]  
;    st [y],1   |   ld r2, [x]
;
;   P: r1 = 1 and r2 = 0
;-----------------------------

(set-option :produce-models true)

; Variable definitions - SSA variables
(declare-fun v_x_0     () (_ BitVec 8))
(declare-fun v_y_0     () (_ BitVec 8))
(declare-fun v_x_T1_1  () (_ BitVec 8))
(declare-fun v_y_T1_1  () (_ BitVec 8))
(declare-fun v_r2_T2_1 () (_ BitVec 8))
(declare-fun v_r1_T2_1 () (_ BitVec 8))

; Variable definitions for Pi-functions
(declare-fun pi_x_T2_1 () (_ BitVec 8))
(declare-fun pi_y_T2_1 () (_ BitVec 8))

; Variable definitions - Timestamps
(declare-fun t1_local  () Int) ; st [x],1 - local
(declare-fun t1_global () Int) ; st [x],1 - global
(declare-fun t2_local  () Int) ; st [y],1 - local
(declare-fun t2_global () Int) ; st [y],1 - global
(declare-fun t3        () Int) ; ld r1, [y]
(declare-fun t4        () Int) ; ld r2, [x]

; State update constraints
(assert (= v_x_0    #x00))
(assert (= v_y_0    #x00))
(assert (= v_x_T1_1 #x01))
(assert (= v_y_T1_1 #x01))
(assert (= v_r2_T2_1 pi_x_T2_1))
(assert (= v_r1_T2_1 pi_y_T2_1))

; Pi-functions
(assert (or (and (= pi_y_T2_1 v_y_T1_1) (< t2_global t3) (or (< 0 t2_global) (< t3 0)))
            (and (= pi_y_T2_1 v_y_0)    (< 0  t3)        (or (< t2_global 0) (< t3 t2_global)))))
(assert (or (and (= pi_x_T2_1 v_x_T1_1) (< t1_global t4) (or (< 0 t1_global) (< t4 0)))
            (and (= pi_x_T2_1 v_x_0)    (< 0  t4)        (or (< t1_global 0) (< t4 t1_global)))))

; Program order
(assert (< 0  t1_local))
(assert (< t1_local t2_local))
(assert (< 0  t3))
(assert (< t3 t4))

; TSO specific
(assert (< t1_local t1_global))
(assert (< t2_local t2_global))
(assert (< t1_global t2_global)) ; t1_local<t2_local => t1_global < t2_global

; Property
(assert (and (= v_r1_T2_1 #x01) (= v_r2_T2_1 #x00)))

; Check
(check-sat)

; Model
; (get-model) ; will be unsat, so no model is available

; The following three properties should be sat
; (assert (and (= v_r1_T2_1 #x00) (= v_r2_T2_1 #x00)))  --> sat
; (assert (and (= v_r1_T2_1 #x00) (= v_r2_T2_1 #x01)))  --> sat
; (assert (and (= v_r1_T2_1 #x01) (= v_r2_T2_1 #x01)))  --> sat