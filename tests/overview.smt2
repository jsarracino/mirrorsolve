(set-logic ALL)
(declare-sort V 0)
( declare-datatype Tree_V ( 
		( E_V )
		( T_V ( proj_T_V_0 Tree_V )( proj_T_V_1 Int )( proj_T_V_2 V )( proj_T_V_3 Tree_V )) 
	) 
)
(declare-fun gt_t (Int Tree_V) Bool)
(assert (not 
    (forall ((fvar_0 Int) (fvar_1 Int)) 
        (=> (> fvar_0 fvar_1) 
        (=> (forall ((fvar_2 Int) (fvar_3 Tree_V) (fvar_4 Int) (fvar_5 V) (fvar_6 Tree_V)) (and (=> (and (> fvar_4 fvar_2) (and (gt_t fvar_2 fvar_3) (gt_t fvar_2 fvar_6))) (gt_t fvar_2 (T_V fvar_3 fvar_4 fvar_5 fvar_6))) (=> (gt_t fvar_2 (T_V fvar_3 fvar_4 fvar_5 fvar_6)) (and (> fvar_4 fvar_2) (and (gt_t fvar_2 fvar_3) (gt_t fvar_2 fvar_6)))))) 
        (=> (forall ((fvar_2 Int)) (and (=> (gt_t fvar_2 E_V) true) (=> true (gt_t fvar_2 E_V)))) (=> (gt_t fvar_0 E_V) (gt_t fvar_1 E_V)))))
    )
))
 

(check-sat)

