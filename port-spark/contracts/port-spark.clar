;; PortSpark Customs Compliance Platform

;; Implements:
;;   - Shipment registration and cargo tracking
;;   - Risk-weighted compliance scoring
;;   - Automated clearance pathways (instant vs multi-sig)
;;   - Compliance Credit System for trusted importers
;;   - Immutable audit trail via on-chain events

;; -------------------------------------------------------
;; Constants
;; -------------------------------------------------------

(define-constant CONTRACT-OWNER tx-sender)

;; Error codes
(define-constant ERR-NOT-AUTHORIZED        (err u100))
(define-constant ERR-SHIPMENT-NOT-FOUND    (err u101))
(define-constant ERR-ALREADY-REGISTERED   (err u102))
(define-constant ERR-INVALID-STATUS       (err u103))
(define-constant ERR-ALREADY-APPROVED     (err u104))
(define-constant ERR-THRESHOLD-NOT-MET    (err u105))
(define-constant ERR-INSPECTOR-EXISTS     (err u106))
(define-constant ERR-INSPECTOR-NOT-FOUND  (err u107))

;; Risk score thresholds (0-100 scale)
;; Scores at or below LOW-RISK-THRESHOLD receive instant clearance
(define-constant LOW-RISK-THRESHOLD  u30)
;; Scores above HIGH-RISK-THRESHOLD require multi-sig approval
(define-constant HIGH-RISK-THRESHOLD u70)

;; Number of inspector approvals required for high-risk shipments
(define-constant MULTISIG-REQUIRED u2)

;; Compliance credit reward per successful clearance
(define-constant CREDIT-REWARD u10)

;; Maximum compliance credits an importer can accumulate
(define-constant MAX-CREDITS u200)

;; -------------------------------------------------------
;; Data Maps
;; -------------------------------------------------------

;; Authorized customs inspectors
(define-map inspectors
  { inspector: principal }
  { active: bool, name: (string-ascii 64) }
)

;; Importer compliance profiles
(define-map importer-profiles
  { importer: principal }
  {
    compliance-credits: uint,    ;; accumulated credit score
    total-shipments:    uint,    ;; total shipments submitted
    cleared-shipments:  uint     ;; total shipments cleared
  }
)

;; Core shipment registry
;; shipment-id: globally unique identifier supplied by caller
(define-map shipments
  { shipment-id: (string-ascii 64) }
  {
    importer:           principal,
    origin-country:     (string-ascii 3),   ;; ISO 3166-1 alpha-3
    destination-country:(string-ascii 3),
    cargo-class:        (string-ascii 16),  ;; HS-code category label
    declared-value:     uint,               ;; in USD cents
    risk-score:         uint,               ;; 0-100 computed at registration
    status:             (string-ascii 16),  ;; "pending" | "cleared" | "flagged" | "rejected"
    clearance-type:     (string-ascii 16),  ;; "instant" | "multisig" | "manual"
    approval-count:     uint,
    block-registered:   uint,
    block-updated:      uint
  }
)

;; Tracks which inspectors have approved a given high-risk shipment
(define-map shipment-approvals
  { shipment-id: (string-ascii 64), inspector: principal }
  { approved: bool }
)

;; -------------------------------------------------------
;; Private Helpers
;; -------------------------------------------------------

;; Compute a deterministic risk score from shipment attributes.
;; In production this would be replaced by an oracle-fed value.
;; Score components (each 0-25, summed to 0-100):
;;   a) declared-value component  - higher value = higher risk
;;   b) destination risk factor   - hardcoded sample; oracle in prod
;;   c) cargo class factor        - hardcoded sample; oracle in prod
;;   d) importer credit offset    - lower credits = higher risk
(define-private (compute-risk-score
    (declared-value uint)
    (destination-country (string-ascii 3))
    (cargo-class (string-ascii 16))
    (importer principal))

  (let (
    ;; Value component: scale declared-value to 0-25
    ;; Cap at 250000000 cents ($2.5M) for scoring purposes
    (value-capped (if (> declared-value u250000000) u250000000 declared-value))
    (value-component (/ (* value-capped u25) u250000000))

    ;; Destination risk: simplified lookup returning 0 | 10 | 25
    (dest-risk (if (is-eq destination-country "USA") u0
                (if (is-eq destination-country "GBR") u5
                (if (is-eq destination-country "CHN") u15
                u20))))

    ;; Cargo class risk: simplified lookup
    (cargo-risk (if (is-eq cargo-class "electronics") u5
                 (if (is-eq cargo-class "chemicals")   u20
                 (if (is-eq cargo-class "textiles")    u5
                 (if (is-eq cargo-class "weapons")     u25
                 u10)))))

    ;; Importer credit offset: max credit holders get -10 risk
    (profile (map-get? importer-profiles { importer: importer }))
    (credits (match profile p (get compliance-credits p) u0))
    (credit-offset (if (>= credits u100) u10 (if (>= credits u50) u5 u0)))
  )
  ;; Sum components and subtract credit offset, floor at 0
  (let ((raw-score (+ value-component dest-risk cargo-risk)))
    (if (> credit-offset raw-score) u0 (- raw-score credit-offset))
  ))
)

;; Determine clearance type from risk score
(define-private (determine-clearance-type (risk-score uint))
  (if (<= risk-score LOW-RISK-THRESHOLD)
    "instant"
    (if (> risk-score HIGH-RISK-THRESHOLD)
      "multisig"
      "manual"
    )
  )
)

;; Determine initial status from clearance type
(define-private (determine-initial-status (clearance-type (string-ascii 16)))
  (if (is-eq clearance-type "instant")
    "cleared"
    "pending"
  )
)

;; Ensure caller is an active inspector
(define-private (is-active-inspector (who principal))
  (match (map-get? inspectors { inspector: who })
    entry (get active entry)
    false
  )
)

;; Ensure caller is contract owner
(define-private (is-owner)
  (is-eq tx-sender CONTRACT-OWNER)
)

;; Increment importer stats and optionally award compliance credits
(define-private (update-importer-stats (importer principal) (award-credit bool))
  (let (
    (profile (default-to
      { compliance-credits: u0, total-shipments: u0, cleared-shipments: u0 }
      (map-get? importer-profiles { importer: importer })))
    (new-credits
      (if award-credit
        (if (< (+ (get compliance-credits profile) CREDIT-REWARD) MAX-CREDITS)
          (+ (get compliance-credits profile) CREDIT-REWARD)
          MAX-CREDITS)
        (get compliance-credits profile)))
    (new-cleared
      (if award-credit
        (+ (get cleared-shipments profile) u1)
        (get cleared-shipments profile)))
  )
  (map-set importer-profiles
    { importer: importer }
    {
      compliance-credits: new-credits,
      total-shipments:    (+ (get total-shipments profile) u1),
      cleared-shipments:  new-cleared
    }
  ))
)

;; -------------------------------------------------------
;; Public Functions - Admin
;; -------------------------------------------------------

;; Register a new customs inspector
(define-public (add-inspector (inspector principal) (name (string-ascii 64)))
  (begin
    (asserts! (is-owner) ERR-NOT-AUTHORIZED)
    (asserts! (is-none (map-get? inspectors { inspector: inspector })) ERR-INSPECTOR-EXISTS)
    (map-set inspectors { inspector: inspector } { active: true, name: name })
    (print { event: "inspector-added", inspector: inspector, name: name })
    (ok true)
  )
)

;; Deactivate an inspector (non-destructive)
(define-public (deactivate-inspector (inspector principal))
  (begin
    (asserts! (is-owner) ERR-NOT-AUTHORIZED)
    (asserts! (is-some (map-get? inspectors { inspector: inspector })) ERR-INSPECTOR-NOT-FOUND)
    (map-set inspectors { inspector: inspector }
      (merge (unwrap-panic (map-get? inspectors { inspector: inspector }))
             { active: false }))
    (print { event: "inspector-deactivated", inspector: inspector })
    (ok true)
  )
)

;; -------------------------------------------------------
;; Public Functions - Importer
;; -------------------------------------------------------

;; Register a new shipment. Computes risk score and sets clearance pathway.
(define-public (register-shipment
    (shipment-id        (string-ascii 64))
    (origin-country     (string-ascii 3))
    (destination-country (string-ascii 3))
    (cargo-class        (string-ascii 16))
    (declared-value     uint))

  (begin
    ;; Prevent duplicate registration
    (asserts! (is-none (map-get? shipments { shipment-id: shipment-id }))
              ERR-ALREADY-REGISTERED)

    (let (
      (importer        tx-sender)
      (risk-score      (compute-risk-score declared-value destination-country cargo-class tx-sender))
      (clearance-type  (determine-clearance-type risk-score))
      (init-status     (determine-initial-status clearance-type))
      (award-credit    (is-eq init-status "cleared"))
    )
    ;; Store shipment record
    (map-set shipments { shipment-id: shipment-id }
      {
        importer:            importer,
        origin-country:      origin-country,
        destination-country: destination-country,
        cargo-class:         cargo-class,
        declared-value:      declared-value,
        risk-score:          risk-score,
        status:              init-status,
        clearance-type:      clearance-type,
        approval-count:      u0,
        block-registered:    block-height,
        block-updated:       block-height
      }
    )
    ;; Update importer stats (increment total, credit if instant-cleared)
    (update-importer-stats importer award-credit)
    (print {
      event:          "shipment-registered",
      shipment-id:    shipment-id,
      importer:       importer,
      risk-score:     risk-score,
      clearance-type: clearance-type,
      status:         init-status
    })
    (ok { risk-score: risk-score, clearance-type: clearance-type, status: init-status }))
  )
)

;; -------------------------------------------------------
;; Public Functions - Inspector
;; -------------------------------------------------------

;; Approve a pending high-risk (multisig) shipment.
;; Once MULTISIG-REQUIRED approvals are collected, the shipment is cleared.
(define-public (approve-shipment (shipment-id (string-ascii 64)))
  (begin
    (asserts! (is-active-inspector tx-sender) ERR-NOT-AUTHORIZED)

    (let ((shipment (unwrap! (map-get? shipments { shipment-id: shipment-id })
                             ERR-SHIPMENT-NOT-FOUND)))
      ;; Shipment must be pending
      (asserts! (is-eq (get status shipment) "pending") ERR-INVALID-STATUS)
      ;; Prevent double-approval by same inspector
      (asserts!
        (is-none (map-get? shipment-approvals { shipment-id: shipment-id, inspector: tx-sender }))
        ERR-ALREADY-APPROVED)

      ;; Record this inspector's approval
      (map-set shipment-approvals
        { shipment-id: shipment-id, inspector: tx-sender }
        { approved: true })

      (let ((new-approval-count (+ (get approval-count shipment) u1)))
        ;; Check if threshold is met
        (if (>= new-approval-count MULTISIG-REQUIRED)
          ;; Clear the shipment
          (begin
            (map-set shipments { shipment-id: shipment-id }
              (merge shipment {
                status:         "cleared",
                approval-count: new-approval-count,
                block-updated:  block-height
              }))
            (update-importer-stats (get importer shipment) true)
            (print {
              event:       "shipment-cleared",
              shipment-id: shipment-id,
              approvals:   new-approval-count,
              inspector:   tx-sender
            })
            (ok { status: "cleared", approval-count: new-approval-count })
          )
          ;; Still accumulating approvals
          (begin
            (map-set shipments { shipment-id: shipment-id }
              (merge shipment {
                approval-count: new-approval-count,
                block-updated:  block-height
              }))
            (print {
              event:              "shipment-approval-added",
              shipment-id:        shipment-id,
              approval-count:     new-approval-count,
              approvals-required: MULTISIG-REQUIRED,
              inspector:          tx-sender
            })
            (ok { status: "pending", approval-count: new-approval-count })
          )
        )
      )
    )
  )
)

;; Flag a shipment for manual review or rejection
(define-public (flag-shipment (shipment-id (string-ascii 64)) (reason (string-ascii 128)))
  (begin
    (asserts! (is-active-inspector tx-sender) ERR-NOT-AUTHORIZED)
    (let ((shipment (unwrap! (map-get? shipments { shipment-id: shipment-id })
                             ERR-SHIPMENT-NOT-FOUND)))
      (asserts! (is-eq (get status shipment) "pending") ERR-INVALID-STATUS)
      (map-set shipments { shipment-id: shipment-id }
        (merge shipment { status: "flagged", block-updated: block-height }))
      (print {
        event:       "shipment-flagged",
        shipment-id: shipment-id,
        reason:      reason,
        inspector:   tx-sender
      })
      (ok true)
    )
  )
)

;; Reject a flagged shipment
(define-public (reject-shipment (shipment-id (string-ascii 64)) (reason (string-ascii 128)))
  (begin
    (asserts! (is-active-inspector tx-sender) ERR-NOT-AUTHORIZED)
    (let ((shipment (unwrap! (map-get? shipments { shipment-id: shipment-id })
                             ERR-SHIPMENT-NOT-FOUND)))
      (asserts!
        (or (is-eq (get status shipment) "flagged")
            (is-eq (get status shipment) "pending"))
        ERR-INVALID-STATUS)
      (map-set shipments { shipment-id: shipment-id }
        (merge shipment { status: "rejected", block-updated: block-height }))
      (print {
        event:       "shipment-rejected",
        shipment-id: shipment-id,
        reason:      reason,
        inspector:   tx-sender
      })
      (ok true)
    )
  )
)

;; -------------------------------------------------------
;; Read-Only Functions
;; -------------------------------------------------------

;; Get full shipment details
(define-read-only (get-shipment (shipment-id (string-ascii 64)))
  (map-get? shipments { shipment-id: shipment-id })
)

;; Get importer compliance profile
(define-read-only (get-importer-profile (importer principal))
  (default-to
    { compliance-credits: u0, total-shipments: u0, cleared-shipments: u0 }
    (map-get? importer-profiles { importer: importer }))
)

;; Check if an inspector has approved a specific shipment
(define-read-only (get-approval-status (shipment-id (string-ascii 64)) (inspector principal))
  (is-some (map-get? shipment-approvals { shipment-id: shipment-id, inspector: inspector }))
)

;; Get inspector info
(define-read-only (get-inspector (inspector principal))
  (map-get? inspectors { inspector: inspector })
)

;; Preview risk score without submitting a shipment
(define-read-only (preview-risk-score
    (declared-value      uint)
    (destination-country (string-ascii 3))
    (cargo-class         (string-ascii 16))
    (importer            principal))
  (let ((score (compute-risk-score declared-value destination-country cargo-class importer)))
    {
      risk-score:     score,
      clearance-type: (determine-clearance-type score)
    }
  )
)
