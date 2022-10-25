(set-logic ALL)
(declare-sort V 0)
( declare-datatype Tree_V ( 
		( E_V )
		( T_V ( proj_T_V_0 Tree_V )( proj_T_V_1 Int )( proj_T_V_2 V )( proj_T_V_3 Tree_V )) 
	) 
)
(declare-fun gt_t (Int Tree_V) Bool)
(assert (not 
    (forall ((x Int) (y Int)) 
        (=> (> x y) 
        (=> (forall ((k Int) (l Tree_V) (kp Int) (v V) (r Tree_V)) 
            (and 
                (=> (and (> kp k) (and (gt_t k l) (gt_t k r))) 
                    (gt_t k (T_V l kp v r))) 
                (=> (gt_t k (T_V l kp v r)) 
                    (and (> kp k) (and (gt_t k l) (gt_t k r)))))) 
        (=> (forall ((x Int)) 
            (and 
                (=> (gt_t x E_V) true) 
                (=> true (gt_t x E_V))
            )) 
        (=> (gt_t x E_V) 
            (gt_t y E_V)
        ))))
    )
))
 
(check-sat)