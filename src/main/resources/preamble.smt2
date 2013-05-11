; Requires Z3 4.x

; ATTENTION: Continuing multi-line statements must be indented with at least
;            one tab or two spaces. All other lines must not start with tabs
;            or more than one space.

; Currently, print-success MUST come first, because it guarantees that every query to Z3, including
; setting options, is answered by a success (or error) reply from Z3. Silicon currently relies on
; these replies when it interacts with Z3 via stdio.
(set-option :print-success true) ; Boogie: false

(set-option :global-decls true) ; Boogie: default
(set-option :AUTO_CONFIG false) ; Usually a good idea

; Don't try to find models. Z3 would otherwise try to find models for uninterpreted (limited)
; functions that come from the program.
(set-option :SMT.MBQI false)

; [Malte] The remaining options were taken from the Boogie preamble when I compared Syxc and
; VCG-Chalice for the VSTTE12 paper. I have no clue what these options do and how important
; they are.
(set-option :MODEL.V2 true)
(set-option :SMT.PHASE_SELECTION 0)
(set-option :SMT.RESTART_STRATEGY 0)
(set-option :SMT.RESTART_FACTOR |1.5|)
(set-option :SMT.ARITH.RANDOM_INITIAL_VALUE true)
; (set-option :SMT.CASE_SPLIT 3) ; Unsupported in Z3 4.3?
(set-option :SMT.DELAY_UNITS true)
(set-option :SMT.DELAY_UNITS_THRESHOLD 16)
(set-option :NNF.SK_HACK true)
(set-option :SMT.QI.EAGER_THRESHOLD 100)
; (set-option :SMT.QI.COST |"(+ weight generation)"|) ; Unsupported in Z3 4.3?
(set-option :TYPE_CHECK true)
(set-option :SMT.BV.REFLECT true)

; (set-option :QI_PROFILE true)
; (set-option :DEFAULT_QID true)

; --- Snapshots ---

(declare-datatypes () ((
    $Snap $Snap.unit
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))

(declare-fun $Snap.snapEq ($Snap $Snap) Bool)

(assert (forall ((x $Snap) (y $Snap)) (!
	(implies
		($Snap.snapEq x y)
		(and (= x y)))
	:qid |$Snap.snapEq|
	:pattern (($Snap.snapEq x y))
	)))

; --- References ---

(declare-sort $Ref)
(declare-const $Ref.null $Ref)

; --- Permissions ---

(define-sort $Perm () Real)
(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)
(declare-const $Perm.iRd $Perm) ; ???
(declare-const $Perm.pRd $Perm) ; Predicate read
(declare-const $Perm.mRd $Perm) ; Monitor read
(declare-const $Perm.cRd $Perm) ; Channel read

(define-fun $Perm.isValid ((p $Perm) (ub $Perm)) Bool
  (and (< $Perm.No p)
       (< p ub)))

(define-fun $Perm.isRead ((p $Perm) (ub $Perm)) Bool
  (and ($Perm.isValid p ub)
       (< (* 1000.0 p) $Perm.Write)))

(assert ($Perm.isRead $Perm.iRd $Perm.Write))
(assert ($Perm.isRead $Perm.mRd $Perm.Write))
(assert
  (and
    (= $Perm.mRd $Perm.pRd )
    (= $Perm.pRd $Perm.cRd )))

; --- Sort wrappers ---

(declare-fun $SortWrappers.$SnapToInt ($Snap) Int)
(declare-fun $SortWrappers.IntTo$Snap (Int) $Snap)

(assert (forall ((x Int))
	(= x ($SortWrappers.$SnapToInt($SortWrappers.IntTo$Snap x)))))

(assert (forall ((x $Snap))
	(= x ($SortWrappers.IntTo$Snap($SortWrappers.$SnapToInt x)))))

(declare-fun $SortWrappers.$SnapTo$Ref ($Snap) $Ref)
(declare-fun $SortWrappers.$RefTo$Snap ($Ref) $Snap)

(assert (forall ((x $Ref))
	(= x ($SortWrappers.$SnapTo$Ref($SortWrappers.$RefTo$Snap x)))))

(assert (forall ((x $Snap))
	(= x ($SortWrappers.$RefTo$Snap($SortWrappers.$SnapTo$Ref x)))))

(declare-fun $SortWrappers.$SnapToBool ($Snap) Bool)
(declare-fun $SortWrappers.BoolTo$Snap (Bool) $Snap)

(assert (forall ((x Bool))
	(= x ($SortWrappers.$SnapToBool($SortWrappers.BoolTo$Snap x)))))

(assert (forall ((x $Snap))
	(= x ($SortWrappers.BoolTo$Snap($SortWrappers.$SnapToBool x)))))

; ; TODO: BoolToInt and BoolToRef are only needed when True is chosen as
; ;        the result value of dead branches. Either prune such branches, i.e.,
; ;        simplify an ite to a implication, or use a fresh term of the
; ;        appropriate sort instead of True.
; (declare-fun $SortWrappers.BoolToInt (Bool) Int)
; (declare-fun $SortWrappers.IntToBool (Int) Bool)

; (assert (forall ((x Bool))
	; (= x ($SortWrappers.IntToBool($SortWrappers.BoolToInt x)))))

; (declare-fun $SortWrappers.BoolTo$Ref (Bool) $Ref)
; (declare-fun $SortWrappers.$RefToBool ($Ref) Bool)

; (assert (forall ((x Bool))
	; (= x ($SortWrappers.$RefToBool($SortWrappers.BoolTo$Ref x)))))

; --- End static preamble ---

; (get-proof "stdout")
; (get-info statistics)

; (push)
; (check-sat)
; (pop)
