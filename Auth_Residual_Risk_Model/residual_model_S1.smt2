;;Fuzzy Goals
(declare-fun AdapAuthR () Real)
(declare-fun Security () Real)
(declare-fun Usability () Real)
(declare-fun Performance() Real)

;;AdapAuthR = Security && Usability && Performance 
(assert (and (<= AdapAuthR 
             (ite (<= Security Usability) 
                  (ite (<= Security Performance) Security  Performance) 
                  (ite (<= Usability Performance) Usability Performance)))))

(declare-fun AvgPerformance() Real)
(declare-fun AVGPerforSum() Real)
(declare-fun  PerforSum () Real)

(assert (and (<= 0 AdapAuthR ) (<= AdapAuthR 1)))
(assert (and (<= 0 Security ) (<= Security 1)))
(assert (and (<= 0 Usability) (<= Usability 1))) 
(assert (and (<= 0 Performance) (<= Performance 1)))
(assert (and (<= 0 AvgPerformance) (<= AvgPerformance 1)))
(assert (and (<= 0 AVGPerforSum  ) (<= AVGPerforSum   1)))

;;Fuzzy Security Goals
(declare-fun  Authenticity() Real)
(declare-fun  Confidentiality () Real)
(declare-fun  Integrity () Real)

;;Security = Authenticity && Confidentiality && Integrity 
(assert (and (<= Security 
             (ite (<= Authenticity Confidentiality) 
                  (ite (<= Authenticity Integrity) Authenticity  Integrity) 
                  (ite (<= Confidentiality Integrity) Confidentiality Integrity))) ))

(declare-fun  AvgAuthenticity() Real)
(declare-fun  AvgConfidentiality () Real)
(declare-fun  AvgIntegrity () Real)
(declare-fun  AuthentPriority () Real)
(declare-fun  ConfPriority  () Real)
(declare-fun  IntegPriority () Real)
(declare-fun  PerformancePriority () Real)

(declare-fun  SumInteg () Real)
(declare-fun  AVGSumInteg () Real)
(declare-fun  SumConf () Real)
(declare-fun  AVGSumConf () Real)
(declare-fun  SumAuth () Real)
(declare-fun  AVGSumAuth () Real)

;;Fuzzy Security Goals
(assert (and (<= 0 Authenticity) (<= Authenticity 1)))
(assert (and (<= 0 Confidentiality) (<= Confidentiality 1)))
(assert (and (<= 0 Integrity) (<= Integrity 1)))

(assert (and (<= 0 AvgAuthenticity) (<= AvgAuthenticity 1)))
(assert (and (<= 0 AvgConfidentiality) (<= AvgConfidentiality 1)))
(assert (and (<= 0 AvgIntegrity) (<= AvgIntegrity 1)))

(assert (and (<= 0 AuthentPriority) (<= AuthentPriority 1)))
(assert (and (<= 0 ConfPriority) (<= ConfPriority 1)))
(assert (and (<= 0 IntegPriority) (<= IntegPriority 1)))
(assert (and (<= 0 PerformancePriority) (<= PerformancePriority 1)))

(assert (and (<= 0 AVGSumInteg) (<= AVGSumInteg 1)))
(assert (and (<= 0 AVGSumAuth ) (<= AVGSumAuth  1)))
(assert (and (<= 0 AVGSumConf ) (<= AVGSumConf 1)))

;;Fuzzy usability Goals
(declare-fun  Effectiveness  () Real)
(declare-fun  Efficiency () Real)

(declare-fun  AvgEfficiency () Real)
(declare-fun  AvgEffectiveness  () Real)

(declare-fun  EffectPriority  () Real)
(declare-fun  EfficPriority () Real)
(declare-fun  EfficSum () Real)
(declare-fun  AVGEfficSum () Real)
(declare-fun  EffetSum () Real)
(declare-fun  AVGEffetSum () Real)

;;Fuzzy usability Goals
(assert (and (<= 0 Effectiveness) (<= Effectiveness 1)))
(assert (and (<= 0 Efficiency) (<= Efficiency 1)))

(assert (and (<= 0 AvgEffectiveness) (<= AvgEffectiveness 1)))
(assert (and (<= 0 AvgEfficiency) (<= AvgEfficiency 1)))

(assert (and (<= 0 EffectPriority) (<= EffectPriority 1)))
(assert (and (<= 0 EfficPriority) (<= EfficPriority 1)))

(assert (and (<= 0 AVGEfficSum  ) (<= AVGEfficSum  1)))
(assert (and (<= 0 AVGEffetSum  ) (<= AVGEffetSum  1)))

;;Utility
(declare-fun Utility () Real)
(assert (and (<= 0 Utility) (<= Utility 1)))
(declare-fun count() Real)  
	     
;;Usability = Effectiveness && Efficiency
(assert (and (<= Usability (ite (<= Effectiveness  Efficiency)  Effectiveness   Efficiency))))

;; The second scenario contextual factors
(declare-fun Location() Real)
(declare-fun InsecNetwork() Real)
(declare-fun UnusualTime() Real)

(declare-fun NightTime () Real)

;; 0 positive and 1 negative
(assert (or (=  Location 0) (= Location 1)))
(assert (or (=  InsecNetwork 0) (= InsecNetwork 1)))
(assert (or (=  UnusualTime 0) (= UnusualTime 1)))
(assert (or (=  NightTime 0) (= NightTime 1)))



;;Operations 
(declare-fun DiagnoseMedicalConditions() Real)      ;; must have
(declare-fun ViewLabResults() Real)                 ;; must have
(declare-fun Controlled() Real)                     ;; nice to have
(declare-fun NonControlled() Real)                  ;; nice to have
(declare-fun AddEncounterNote() Real)               ;; optional
(declare-fun AddReferralNote() Real)                ;; optional
(declare-fun GenerateReports() Real)                ;; optional

;; Operations values 
(assert (or (=  DiagnoseMedicalConditions 0) (= DiagnoseMedicalConditions 1)))
(assert (or (=  ViewLabResults 0) (= ViewLabResults 1)))
(assert (or (=  Controlled 0) (= Controlled 1)))
(assert (or (=  NonControlled 0) (= NonControlled 1)))
(assert (or (=  AddEncounterNote 0) (= AddEncounterNote 1)))
(assert (or (=  AddReferralNote 0) (= AddReferralNote 1)))
(assert (or (=  GenerateReports 0) (= GenerateReports 1)))

;; Assets
(declare-fun Diagnosis() Real)
(declare-fun TreatmentPlan() Real)
(declare-fun LabResults() Real)
(declare-fun TestReports() Real)
(declare-fun NonControlledPrescriptions() Real)
(declare-fun PatientHistory() Real)
(declare-fun ControlledPrescriptions() Real)
(declare-fun PatientInteractions() Real)
(declare-fun VisitSummaries() Real)
(declare-fun ReferralNotes() Real)
(declare-fun EncounterNotes() Real)
(declare-fun PatientRecords() Real)



;; --- Asset Permission Declarations and Sensitivity Ranges ---

;; Diagnosis
(declare-fun Diagnosis_Read () Bool)
(declare-fun Diagnosis_Write () Bool)
(declare-fun Diagnosis_Update () Bool)
(declare-fun Diagnosis_Delete () Bool)
(declare-fun DiagnosisSensitivity () Real)
(assert
  (ite Diagnosis_Delete
    (and (>= DiagnosisSensitivity 0.67) (<= DiagnosisSensitivity 0.7))
    (ite Diagnosis_Update
      (and (>= DiagnosisSensitivity 0.64) (<= DiagnosisSensitivity 0.67))
      (ite Diagnosis_Write
        (and (>= DiagnosisSensitivity 0.6) (<= DiagnosisSensitivity 0.64))
        (and (>= DiagnosisSensitivity 0.5) (<= DiagnosisSensitivity 0.6))
      )
    )
  )
)

;; TreatmentPlan
(declare-fun TreatmentPlan_Read () Bool)
(declare-fun TreatmentPlan_Write () Bool)
(declare-fun TreatmentPlan_Update () Bool)
(declare-fun TreatmentPlan_Delete () Bool)
(declare-fun TreatmentPlanSensitivity () Real)
(assert
  (ite TreatmentPlan_Delete
    (and (>= TreatmentPlanSensitivity 0.57) (<= TreatmentPlanSensitivity 0.6))
    (ite TreatmentPlan_Update
      (and (>= TreatmentPlanSensitivity 0.54) (<= TreatmentPlanSensitivity 0.57))
      (ite TreatmentPlan_Write
        (and (>= TreatmentPlanSensitivity 0.5) (<= TreatmentPlanSensitivity 0.54))
        (and (>= TreatmentPlanSensitivity 0.4) (<= TreatmentPlanSensitivity 0.5))
      )
    )
  )
)

;; LabResults
(declare-fun LabResults_Read () Bool)
(declare-fun LabResults_Write () Bool)
(declare-fun LabResults_Update () Bool)
(declare-fun LabResults_Delete () Bool)
(declare-fun LabResultsSensitivity () Real)
(assert
  (ite LabResults_Delete
    (and (>= LabResultsSensitivity 0.57) (<= LabResultsSensitivity 0.6))
    (ite LabResults_Update
      (and (>= LabResultsSensitivity 0.54) (<= LabResultsSensitivity 0.57))
      (ite LabResults_Write
        (and (>= LabResultsSensitivity 0.5) (<= LabResultsSensitivity 0.54))
        (and (>= LabResultsSensitivity 0.4) (<= LabResultsSensitivity 0.5))
      )
    )
  )
)

;; TestReports
(declare-fun TestReports_Read () Bool)
(declare-fun TestReports_Write () Bool)
(declare-fun TestReports_Update () Bool)
(declare-fun TestReports_Delete () Bool)
(declare-fun TestReportsSensitivity () Real)
(assert
  (ite TestReports_Delete
    (and (>= TestReportsSensitivity 0.57) (<= TestReportsSensitivity 0.6))
    (ite TestReports_Update
      (and (>= TestReportsSensitivity 0.54) (<= TestReportsSensitivity 0.57))
      (ite TestReports_Write
        (and (>= TestReportsSensitivity 0.5) (<= TestReportsSensitivity 0.54))
        (and (>= TestReportsSensitivity 0.4) (<= TestReportsSensitivity 0.5))
      )
    )
  )
)

;; NonControlledPrescriptions
(declare-fun NonControlledPrescriptions_Read () Bool)
(declare-fun NonControlledPrescriptions_Write () Bool)
(declare-fun NonControlledPrescriptions_Update () Bool)
(declare-fun NonControlledPrescriptions_Delete () Bool)
(declare-fun NonControlledPrescriptionsSensitivity () Real)
(assert
  (ite NonControlledPrescriptions_Delete
    (and (>= NonControlledPrescriptionsSensitivity 0.67) (<= NonControlledPrescriptionsSensitivity 0.7))
    (ite NonControlledPrescriptions_Update
      (and (>= NonControlledPrescriptionsSensitivity 0.64) (<= NonControlledPrescriptionsSensitivity 0.67))
      (ite NonControlledPrescriptions_Write
        (and (>= NonControlledPrescriptionsSensitivity 0.6) (<= NonControlledPrescriptionsSensitivity 0.64))
        (and (>= NonControlledPrescriptionsSensitivity 0.5) (<= NonControlledPrescriptionsSensitivity 0.6))
      )
    )
  )
)

;; PatientHistory
(declare-fun PatientHistory_Read () Bool)
(declare-fun PatientHistory_Write () Bool)
(declare-fun PatientHistory_Update () Bool)
(declare-fun PatientHistory_Delete () Bool)
(declare-fun PatientHistorySensitivity () Real)
(assert
  (ite PatientHistory_Delete
    (and (>= PatientHistorySensitivity 0.77) (<= PatientHistorySensitivity 0.8))
    (ite PatientHistory_Update
      (and (>= PatientHistorySensitivity 0.74) (<= PatientHistorySensitivity 0.77))
      (ite PatientHistory_Write
        (and (>= PatientHistorySensitivity 0.7) (<= PatientHistorySensitivity 0.74))
        (and (>= PatientHistorySensitivity 0.65) (<= PatientHistorySensitivity 0.7))
      )
    )
  )
)

;; ControlledPrescriptions
(declare-fun ControlledPrescriptions_Read () Bool)
(declare-fun ControlledPrescriptions_Write () Bool)
(declare-fun ControlledPrescriptions_Update () Bool)
(declare-fun ControlledPrescriptions_Delete () Bool)
(declare-fun ControlledPrescriptionsSensitivity () Real)
(assert
  (ite ControlledPrescriptions_Delete
    (and (>= ControlledPrescriptionsSensitivity 0.86) (<= ControlledPrescriptionsSensitivity 0.87))
    (ite ControlledPrescriptions_Update
      (and (>= ControlledPrescriptionsSensitivity 0.84) (<= ControlledPrescriptionsSensitivity 0.86))
      (ite ControlledPrescriptions_Write
        (and (>= ControlledPrescriptionsSensitivity 0.8) (<= ControlledPrescriptionsSensitivity 0.84))
        (and (>= ControlledPrescriptionsSensitivity 0.75) (<= ControlledPrescriptionsSensitivity 0.8))
      )
    )
  )
)

;; PatientInteractions
(declare-fun PatientInteractions_Read () Bool)
(declare-fun PatientInteractions_Write () Bool)
(declare-fun PatientInteractions_Update () Bool)
(declare-fun PatientInteractions_Delete () Bool)
(declare-fun PatientInteractionsSensitivity () Real)
(assert
  (ite PatientInteractions_Delete
    (and (>= PatientInteractionsSensitivity 0.86) (<= PatientInteractionsSensitivity 0.88))
    (ite PatientInteractions_Update
      (and (>= PatientInteractionsSensitivity 0.84) (<= PatientInteractionsSensitivity 0.86))
      (ite PatientInteractions_Write
        (and (>= PatientInteractionsSensitivity 0.8) (<= PatientInteractionsSensitivity 0.84))
        (and (>= PatientInteractionsSensitivity 0.75) (<= PatientInteractionsSensitivity 0.8))
      )
    )
  )
)

;; VisitSummaries
(declare-fun VisitSummaries_Read () Bool)
(declare-fun VisitSummaries_Write () Bool)
(declare-fun VisitSummaries_Update () Bool)
(declare-fun VisitSummaries_Delete () Bool)
(declare-fun VisitSummariesSensitivity () Real)
(assert
  (ite VisitSummaries_Delete
    (and (>= VisitSummariesSensitivity 0.77) (<= VisitSummariesSensitivity 0.8))
    (ite VisitSummaries_Update
      (and (>= VisitSummariesSensitivity 0.74) (<= VisitSummariesSensitivity 0.77))
      (ite VisitSummaries_Write
        (and (>= VisitSummariesSensitivity 0.7) (<= VisitSummariesSensitivity 0.74))
        (and (>= VisitSummariesSensitivity 0.65) (<= VisitSummariesSensitivity 0.7))
      )
    )
  )
)

;; ReferralNotes
(declare-fun ReferralNotes_Read () Bool)
(declare-fun ReferralNotes_Write () Bool)
(declare-fun ReferralNotes_Update () Bool)
(declare-fun ReferralNotes_Delete () Bool)
(declare-fun ReferralNotesSensitivity () Real)
(assert
  (ite ReferralNotes_Delete
    (and (>= ReferralNotesSensitivity 0.67) (<= ReferralNotesSensitivity 0.7))
    (ite ReferralNotes_Update
      (and (>= ReferralNotesSensitivity 0.64) (<= ReferralNotesSensitivity 0.67))
      (ite ReferralNotes_Write
        (and (>= ReferralNotesSensitivity 0.6) (<= ReferralNotesSensitivity 0.64))
        (and (>= ReferralNotesSensitivity 0.55) (<= ReferralNotesSensitivity 0.6))
      )
    )
  )
)

;; EncounterNotes
(declare-fun EncounterNotes_Read () Bool)
(declare-fun EncounterNotes_Write () Bool)
(declare-fun EncounterNotes_Update () Bool)
(declare-fun EncounterNotes_Delete () Bool)
(declare-fun EncounterNotesSensitivity () Real)
(assert
  (ite EncounterNotes_Delete
    (and (>= EncounterNotesSensitivity 0.67) (<= EncounterNotesSensitivity 0.7))
    (ite EncounterNotes_Update
      (and (>= EncounterNotesSensitivity 0.64) (<= EncounterNotesSensitivity 0.67))
      (ite EncounterNotes_Write
        (and (>= EncounterNotesSensitivity 0.6) (<= EncounterNotesSensitivity 0.64))
        (and (>= EncounterNotesSensitivity 0.55) (<= EncounterNotesSensitivity 0.6))
      )
    )
  )
)

;; PatientRecords
(declare-fun PatientRecords_Read () Bool)
(declare-fun PatientRecords_Write () Bool)
(declare-fun PatientRecords_Update () Bool)
(declare-fun PatientRecords_Delete () Bool)
(declare-fun PatientRecordsSensitivity () Real)
(assert
  (ite PatientRecords_Delete
    (and (>= PatientRecordsSensitivity 0.97) (<= PatientRecordsSensitivity 1.0))
    (ite PatientRecords_Update
      (and (>= PatientRecordsSensitivity 0.94) (<= PatientRecordsSensitivity 0.97))
      (ite PatientRecords_Write
        (and (>= PatientRecordsSensitivity 0.92) (<= PatientRecordsSensitivity 0.94))
        (and (>= PatientRecordsSensitivity 0.9) (<= PatientRecordsSensitivity 0.92))
      )
    )
  )
)

;; ---------------- Hierarchical Permission Logic (Cumulative Authorization) ----------------
;; For each asset: Delete ⇒ Update ⇒ Write ⇒ Read

(define-fun HierarchicalPermissions ((Delete Bool) (Update Bool) (Write Bool) (Read Bool)) Bool
  (and
    (=> Delete Update)
    (=> Delete Write)
    (=> Delete Read)
    (=> Update Write)
    (=> Update Read)
    (=> Write Read)
  )
)



;; Asset value is >= 0 and <= 1
;; Asset value is >= 0 and <= 1
(assert (or (=  Diagnosis 0) (= Diagnosis 1)))
(assert (ite (or (> DiagnoseMedicalConditions 0) (> NonControlled 0) (> Controlled 0) (> GenerateReports 0))(> Diagnosis 0)(= Diagnosis 0) ))

(assert (or (=  TreatmentPlan 0) (= TreatmentPlan 1)))
(assert (ite (or (> DiagnoseMedicalConditions 0) (> GenerateReports 0))(> TreatmentPlan 0)(= TreatmentPlan 0) ))

(assert (or (=  LabResults 0) (= LabResults 1)))
(assert (ite (or (> ViewLabResults 0) (> GenerateReports 0))(> LabResults 0)(= LabResults 0) ))

(assert (or (=  TestReports 0) (= TestReports 1)))
(assert (ite (> ViewLabResults 0) (> TestReports 0) (= TestReports 0) ))

(assert (or (=  NonControlledPrescriptions 0) (= NonControlledPrescriptions 1)))
(assert (ite (> NonControlled 0) (> NonControlledPrescriptions 0) (= NonControlledPrescriptions 0) ))

(assert (or (=  PatientHistory 0) (= PatientHistory 1)))
(assert (ite (or (> Controlled 0) (> NonControlled 0))(> PatientHistory 0)(= PatientHistory 0) ))

(assert (or (=  ControlledPrescriptions 0) (= ControlledPrescriptions 1)))
(assert (ite (> Controlled 0) (> ControlledPrescriptions 0) (= ControlledPrescriptions 0) ))

(assert (or (=  PatientInteractions 0) (= PatientInteractions 1)))
(assert (ite (> AddEncounterNote 0) (> PatientInteractions 0) (= PatientInteractions 0) ))

(assert (or (=  VisitSummaries 0) (= VisitSummaries 1)))
(assert (ite (> AddEncounterNote 0) (> VisitSummaries 0)(= VisitSummaries 0) ))

(assert (or (=  ReferralNotes 0) (= ReferralNotes 1)))
(assert (ite (> AddReferralNote 0) (> ReferralNotes 0) (= ReferralNotes 0) ))

(assert (or (=  EncounterNotes 0) (= EncounterNotes 1)))
(assert (ite (> AddReferralNote 0) (> EncounterNotes 0) (= EncounterNotes 0) ))

(assert (or (=  PatientRecords 0) (= PatientRecords 1)))
(assert (ite (> GenerateReports 0) (> PatientRecords 0) (= PatientRecords 0) ))


(declare-fun CredType () Real)
(declare-fun SomeKnow() Real)
(declare-fun SomeHave () Real)
(declare-fun Signature () Real)
(declare-fun SomeAre() Real)
(declare-fun TwoFactor() Real)
(declare-fun PassStr() Real)
(declare-fun PinLeng() Real)
(declare-fun OtpLeng() Real)

(declare-fun Certificate () Real)
(declare-fun SmartCard () Real)
(declare-fun Token () Real)
(declare-fun Face () Real)
(declare-fun Iris() Real)
(declare-fun Fingerprint() Real) 
(declare-fun SignCryp () Real)
(declare-fun GroupSign() Real)
(declare-fun RingSign () Real)

;; setup the count variable
(assert (ite (> TwoFactor 0) (= count 2) (= count 1)))

;; CRISP Authentication Methods
(assert (or (=  Certificate 0) (= Certificate 1)))
(assert (or (=  SmartCard 0) (= SmartCard 1)))
(assert (or (=  Token 0) (= Token 1)))
(assert (or (=  Face 0) (= Face 1)))
(assert (or (=  Iris 0) (= Iris 1)))
(assert (or (=  Fingerprint 0) (= Fingerprint 1)))
(assert (or (=  SignCryp 0) (= SignCryp 1)))
(assert (or (=  GroupSign 0) (= GroupSign 1)))
(assert (or (=  RingSign 0) (= RingSign 1)))
(declare-fun CredRnew () Real)
(declare-fun CredRnewFactor () Real)

;; FUZZY Authentication Methods
(assert (and (< 0 CredType) (<= CredType 1)))
(assert (and (<= 0 SomeKnow) (<=  SomeKnow 1)))
(assert (and (<= 0 SomeHave) (<= SomeHave 1)))
(assert (and (<= 0 Signature) (<= Signature 1)))
(assert (and (<= 0 SomeAre) (<= SomeAre 1)))
(assert (and (<= 0 TwoFactor) (<= TwoFactor 1)))

;; PassStr= short(0.5) || medium (0.7) ||  Long(1.0)
(assert (or (=  PassStr 0.0) (=  PassStr 0.5) (= PassStr 0.7) (= PassStr 1.0)))

;; PinLeng= short(0.5) || medium (0.7) ||  Long(1.0)
(assert (or (=  PinLeng 0.0) (=  PinLeng 0.5) (= PinLeng 0.7) (= PinLeng 1.0)))
;; OtpLeng= short(0.5) || medium (0.7) ||  Long(1.0)
(assert (or (=  OtpLeng 0.0) (=  OtpLeng 0.5) (= OtpLeng 0.7) (= OtpLeng 1.0)))
 
;;;;;;;;;;;;;;;;;;;;Authentication methods;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;Assign value to CredType;;;;;;;;;;
(assert (= CredType (ite (> TwoFactor 0) TwoFactor
                          (ite (>= SomeKnow SomeHave)
                               (ite (>= SomeKnow  SomeAre) SomeKnow SomeAre) 
                               (ite (>= SomeHave SomeAre) SomeHave SomeAre)) 
)))

;;TwoFactor =  Select two from (SomeKnow, SomeHave, SomeAre)
(assert (ite (and (> SomeKnow 0) (> SomeHave 0))
             (and (> TwoFactor 0) (= SomeAre 0)) true))

(assert (ite (and (> SomeAre 0) (> SomeHave 0))
             (and (> TwoFactor 0) (= SomeKnow 0)) true))

(assert (ite (and (> SomeAre 0) (> SomeKnow 0))
             (and (> TwoFactor 0) (= SomeHave 0)) true))

(assert (ite (> TwoFactor 0) (or (and (> SomeAre 0) (> SomeHave 0) (= SomeKnow 0)) 
                                 (and (> SomeHave 0) (> SomeKnow 0) (= SomeAre 0)) 
                                 (and (> SomeKnow 0) (> SomeAre 0) (= SomeHave 0))) true))

;;TwoFactor value = Max(1, MAX(SomeKnow,SomeHave,SomeAre) + 0.2)
;;0.2 is the impact of the weakiest auth method
(assert (ite (and (> SomeKnow 0) (> SomeHave 0)) 
              (= TwoFactor (ite (> SomeKnow SomeHave) (ite (< SomeKnow 0.8) (+ SomeKnow 0.2) 1) (ite (< SomeHave 0.8) (+ SomeHave 0.2) 1)) ) true))

(assert (ite (and (> SomeAre 0) (> SomeHave 0)) 
              (= TwoFactor (ite (> SomeAre SomeHave) (ite (< SomeAre 0.8) (+ SomeAre 0.2) 1) (ite (< SomeHave 0.8) (+ SomeHave 0.2) 1)) ) true))

(assert (ite (and (> SomeAre 0) (> SomeKnow 0)) 
              (= TwoFactor (ite (> SomeAre SomeKnow) (ite (< SomeAre 0.8) (+ SomeAre 0.2) 1) (ite (< SomeKnow 0.8) (+ SomeKnow 0.2) 1)) ) true))
;;if TwoFactor = 0 then Choose one between (SomeKnow, SomeHave, SomeAre)
(assert (ite (and (= TwoFactor 0) (> SomeKnow 0)) (and (= SomeAre 0) (= SomeHave 0)) true))
(assert (ite (and (= TwoFactor 0) (> SomeHave 0)) (and (= SomeAre 0) (= SomeKnow 0)) true))
(assert (ite (and (= TwoFactor 0) (> SomeAre 0)) (and (= SomeKnow 0) (= SomeHave 0)) true))

;;SomeKnow = MAX (PinLeng,PassStr,OtpLeng)
(assert (= SomeKnow (ite (>= PinLeng PassStr)
                    (ite (>= PinLeng OtpLeng) PinLeng OtpLeng )
                    (ite (>= PassStr OtpLeng) PassStr OtpLeng ))))

;; Choose only one from (PinLeng,PassStr,OtpLeng)
(assert (ite (> PinLeng 0) (and (= PassStr 0) (= OtpLeng 0)) true))
(assert (ite (> PassStr 0) (and (= PinLeng 0) (= OtpLeng 0)) true))
(assert (ite (> OtpLeng 0) (and (= PassStr 0) (= PinLeng 0)) true))

;;SomeHave = MAX (Certificate, SmartCard, Signature)  
(assert (= SomeHave (ite (>= Certificate SmartCard) 
		               (ite (>= Certificate Signature) Certificate Signature) 
	                         (ite (>= SmartCard  Signature) SmartCard Signature))))    

;; Choose only one from (Certificate, SmartCard, Signature)
(assert (ite (> Certificate 0) (and (= SmartCard 0) (= Signature 0)) true))

(assert (ite (> SmartCard 0) (and (= Certificate 0) (= Signature 0)) true))

(assert (ite (> Signature 0) (and (= Certificate 0) (= SmartCard 0)) true))

;;Signature = MAX (Token,SignCryp, GroupSign, RingSign)
(assert (= Signature (ite (>= Token SignCryp )
                          (ite (>= Token  GroupSign)
                               (ite (>= Token  RingSign ) Token  RingSign) 
                               (ite (>= GroupSign   RingSign ) GroupSign RingSign)) 
		    (ite (>= SignCryp GroupSign) 
	                 (ite (>= SignCryp  RingSign) SignCryp  RingSign) 
	                 (ite (>= GroupSign RingSign) GroupSign RingSign))
)))

;; Choose only one between (Token, SignCryp, GroupSign, RingSign)
(assert (ite (> Token 0) (and (= SignCryp 0) (= GroupSign 0) (= RingSign 0)) true))

(assert (ite (> SignCryp 0) (and (= Token 0) (= GroupSign 0) (= RingSign 0)) true))

(assert (ite (> GroupSign 0) (and (= Token 0) (= SignCryp 0) (= RingSign 0)) true))

(assert (ite (> RingSign 0) (and (= Token 0) (= SignCryp 0) (= GroupSign 0)) true))

;;SomeAre = MAX (Face,Iris,Fingerprint)
(assert (= SomeAre (ite (>= Face Iris)
                        (ite (>= Face Fingerprint) Face Fingerprint)
                        (ite (>= Iris Fingerprint) Iris Fingerprint ))))

;;;;Choose only one between (Face,Iris,Fingerprint)               
(assert (ite (> Face 0) (and (= Iris 0) (= Fingerprint 0)) true))
(assert (ite (> Iris 0) (and (= Face 0) (= Fingerprint 0)) true))
(assert (ite (> Fingerprint 0) (and (= Face 0) (= Iris 0)) true))

;;Automation level
(declare-fun AutoLevel () Real)

;; AutoLevel = Not-Automated (0)|| semi-Automated (0.5) || FullAutomated(1.0)
;; PIN&Password&OTP are not automated 
(assert (ite (or (> PinLeng 0) (> PassStr 0) (> OtpLeng 0)) (= AutoLevel 0) 
        (ite (or (> Token 0) (> SmartCard 0) (> Fingerprint 0)(> Face 0)(> Iris 0) (> SignCryp 0) (> GroupSign 0)
           (> RingSign 0)) (= AutoLevel 0.5)
              (= AutoLevel 1) )))

;;;; CredRnew => (Face&Iris&Fingerprint are not Renewal(0) || Daily(0.90) || Weekly(0.50) || Monthly(0.30) || Yearly(0.10) )

(assert (ite (> SomeKnow 0)  
                  (or (= CredRnew  0.90) (= CredRnew 0.50) (= CredRnew 0.30) (= CredRnew 0.10))    
                  (= CredRnew  0)))

;; DevType
;;(declare-fun DevType () Real)
(declare-fun PC () Real)
(declare-fun LapTop () Real)
(declare-fun Phone () Real)
(declare-fun Reader () Real)
(declare-fun Camera () Real)
(declare-fun Scanner () Real)

(assert (or (=  PC 0) (= PC 1)))
(assert (or (=  LapTop 0) (= LapTop 1)))
(assert (or (=  Reader 0) (= Reader 1)))
(assert (or (=  Phone 0) (= Phone 1)))
(assert (or (=  Camera 0) (= Camera 1)))
(assert (or (=  Scanner 0) (= Scanner 1)))

;; DevType (PC,LapTop,Phone,Reader, Camera, Scanner)               
(assert (ite (or (> PinLeng 0) (> PassStr 0) (> OtpLeng 0) (> Certificate 0) (> Token 0) (> SignCryp 0) (> GroupSign 0) (> RingSign 0))  (or (> PC 0) (> LapTop 0) (> Phone 0)) true))  

(assert (ite (or  (> Face 0) (> Iris 0) ) (> Camera 0) true ))
(assert (ite  (>  Fingerprint 0)   (> Scanner 0) true ))
(assert (ite  (>  SmartCard  0)    (> Reader 0)  true )) 

;;;;;;;;;;;;;;;;;;Impact on the requirements;;;;;;;;;;;;;;;;;;

;; SUM (authentication methods  impact on the Confidentiality psitive (0.5) very positively (0.8) , negative (0.3), very negative(0.1) and not impact (0)                                                                                                                           
(assert (= SumConf (+ (* PinLeng  0.5) 
                               (* PassStr 0.5)
                               (* OtpLeng 0.5) 
                               (* Certificate 0.8)
                               (* SmartCard 0.6)
                               (* Token 0.8)
                               (* SignCryp 0.8)
                               (* GroupSign 0.8)
                               (* RingSign 0.8 )
                               (* Iris 0.8)
                               (* Face 0.8)
                               (* Fingerprint 0.8) ) 
                                  ))

;; Avg Sum Confidentiality                              
;;(assert (= AVGSumConf (/ SumConf  count) ))

(assert (ite (> count 1)
		(ite (> SumConf 1) (= AVGSumConf 1) (= AVGSumConf SumConf))
		(= AVGSumConf SumConf) ))

;; Credential Renewal Discount Factor
(assert (= CredRnewFactor  (/ (- 1 CredRnew) 2))) 

;; the impact of  CredRnew on the Confidentiality 
(assert (ite (> SomeKnow 0)
             (ite (>= AVGSumConf CredRnew)
                  (= AvgConfidentiality (ite (> 0 (- AVGSumConf CredRnewFactor)) 0 (- AVGSumConf CredRnewFactor)))
                  (= AvgConfidentiality (ite (> 1 (+ AVGSumConf CredRnewFactor)) (+ AVGSumConf CredRnewFactor) 1))) true))  

(assert (ite (= SomeKnow 0) (= AvgConfidentiality AVGSumConf) true))

;;; SUM (authentication methods  impact on the Authenticity positive (0.5) very positively (0.8) , negative (0.3), very negative(0.1) and not impact (0)                                                           
(assert (= SumAuth (+ (* PinLeng 0.1) 
                      (* PassStr 0.1)  
                      (* OtpLeng 0.1) 
                      (* Certificate 0.8 )
                      (* SmartCard 0.5 )
                      (* Token  0.5)
                      (* SignCryp 0.8)
                      (* GroupSign 0.8)
                      (* RingSign 0.8)
                      (* Iris  0.5)
                      (* Face 0.5)
                      (* Fingerprint 0.5))
                                  )) 
     
;; Avg Authenticity                                   
;;(assert (= AVGSumAuth  (/ SumAuth  count) )) 

(assert (ite (> count 1) 
		(ite (> SumAuth 1) (= AVGSumAuth 1) (= AVGSumAuth SumAuth)) (= AVGSumAuth SumAuth) ))

;; The average auth
(assert (= AvgAuthenticity   AVGSumAuth)) 

                                             
;; SUM(authentication methods  impact on the Integrity psitive (0.5) very positively (0.8) , negative (0.3), very negative(0.1) and not impact (0)              
(assert (= SumInteg (+ (* PinLeng  0.5) 
                               (* PassStr 0.5)
                               (* OtpLeng 0.5) 
                               (* Certificate 0.8)
                               (* SmartCard 0.6)
                               (* Token 0.8)
                               (* SignCryp 0.8)
                               (* GroupSign 0.8)
                               (* RingSign 0.8 )
                               (* Iris 0.8)
                               (* Face 0.8)
                               (* Fingerprint 0.8) )
                                  )) 


 ;; AvgIntegrity                                   
 ;;(assert (= AVGSumInteg (/ SumInteg  count) ))  

(assert (ite (> count 1) 
		(ite (> SumInteg 1) (= AVGSumInteg 1) (= AVGSumInteg SumInteg)) 
		(= AVGSumInteg SumInteg) ))

;; the impact of  CredRnew on the Integrity  
;; the impact of  CredRnew on the Confidentiality 
(assert (ite (> SomeKnow 0)
             (ite (>= AVGSumInteg CredRnew)
                  (= AvgIntegrity (ite (> 0 (- AVGSumInteg CredRnewFactor)) 0 (- AVGSumInteg CredRnewFactor)))
                  (= AvgIntegrity (ite (> 1 (+ AVGSumInteg CredRnewFactor)) (+ AVGSumInteg CredRnewFactor) 1))) true))  

;; I added the AvgIntegrity in case that SomeKnow not greater than 0
(assert (ite (= SomeKnow 0) (= AvgIntegrity AVGSumInteg) true))       
                                  
;;SUM (authentication methods  impact on the Efficiency psitive (0.5) very positively (0.8) , negative (0.3), very negative(0.1) and not impact (0)                          
(assert (= EfficSum  (+ (* PinLeng 0.3)
                              (* PassStr 0.3)
                              (* OtpLeng 0.3) 
                              (* Certificate 0.1)
                              (* SmartCard 0.6)
                              (* Token 0.5)
                              (* SignCryp 0.1)
                              (* GroupSign 0.1)
                              (* RingSign 0.1)
                              (* Iris 0.5)
                              (* Face 0.5)
                              (* Fingerprint 0.5)  )
                                  ))


;; having two authentication methods should reduce the usability
(assert (ite (> TwoFactor 0) (= AVGEfficSum (/ EfficSum  count)) (= AVGEfficSum (/ EfficSum  count)) ))
 
;; AvgEfficiency =MAX (AVGEfficSum , AutoLevel)                                         
(assert  (ite (> AVGEfficSum AutoLevel) 
               (= AvgEfficiency AVGEfficSum)                                                
               (= AvgEfficiency AutoLevel)))

;; SUM (authentication methods  impact on the Effectiveness psitive (0.5) very positively (0.8) , negative (0.3), very negative(0.1) and not impact (0)                          
(assert (= EffetSum  (+ (* PinLeng 0.1)
                                 (* PassStr 0.1)
                                 (* OtpLeng 0.1) 
                                 (* Certificate 0.4)
                                 (* SmartCard 0.6)
                                 (* Token 0.5)
                                 (* SignCryp 0.8)
                                 (* GroupSign 0.8)
                                 (* RingSign 0.8)
                                 (* Iris 0.5)
                                 (* Face 0.5)
                                 (* Fingerprint 0.5) )
                                  )) 

;; Avg Effectiveness                                   
;; having two authentication methods should reduce the usability
;; having two authentication methods should reduce the usability
(assert (ite (> TwoFactor 0) (= AVGEffetSum (/ EffetSum  count)) (= AVGEffetSum (/ EffetSum  count)) ))

;;AvgEffectiveness =MAX(AVGEffetSum ,(- 1 CredRnew), AutoLevel )
(assert  (ite (>= AVGEffetSum (-  1 CredRnew))
              (ite (>= AVGEffetSum  AutoLevel) 
                   (= AvgEffectiveness AVGEffetSum) 
                   (= AvgEffectiveness AutoLevel))
              (ite (>= (-  1 CredRnew)  AutoLevel) 
                   (= AvgEffectiveness (-  1 CredRnew)) 
                   (= AvgEffectiveness AutoLevel))
))

;; SUM (authentication methods impact on the Performance psitive (0.5) very positively (0.8) , negative (0.3), very negative(0.1) and not impact (0)                          
(assert (= PerforSum  (+ (* PinLeng 0.8)
                               (* PassStr 0.8)
                               (* OtpLeng 0.8) 
                               (* Certificate 0.1)
                               (* SmartCard 0.6)
                               (* Token 0.5)
                               (* SignCryp 0.1)
                               (* GroupSign 0.1)
                               (* RingSign 0.1)
                               (* Iris 0.3)
                               (* Face 0.3)
                               (* Fingerprint 0.5) )
                                  ))
  
;; Avg Performance 
;; having two authentication methods should reduce the usability
(assert (ite (> TwoFactor 0) (= AVGPerforSum (/ PerforSum  count)) (= AVGPerforSum PerforSum  ) ))

(assert (= AvgPerformance AVGPerforSum) )
 
;;  AutoLevel
;; (assert  (ite (>= AVGPerforSum  AutoLevel) 
;;               (= AvgPerformance AVGPerforSum)   
;;               (= AvgPerformance AutoLevel))) 



(define-fun Aggregate ((A Real) (B Real)) Real
  (ite (>= A B) A B)
)

(declare-fun AssetValue() Real)

(assert (and (>= AssetValue 0) (<= AssetValue 1))) 




(assert (= AssetValue
  (+ (* Diagnosis DiagnosisSensitivity 0.2)
     (* TreatmentPlan TreatmentPlanSensitivity 0.2)
     (* LabResults LabResultsSensitivity 0.1)
     (* TestReports TestReportsSensitivity 0.05)
     (* NonControlledPrescriptions NonControlledPrescriptionsSensitivity 0.1)
     (* PatientHistory PatientHistorySensitivity 0.15)
     (* ControlledPrescriptions ControlledPrescriptionsSensitivity 0.1)
     (* PatientInteractions PatientInteractionsSensitivity 0.05)
     (* VisitSummaries VisitSummariesSensitivity 0.1)
     (* ReferralNotes ReferralNotesSensitivity 0.05)
     (* EncounterNotes EncounterNotesSensitivity 0.05)
     (* PatientRecords PatientRecordsSensitivity 0.15))
))



;;---------------------------------
;;;;The contextual factors impact on the requirements priority

;; The impact of the unfamiliar location or the unusual time on the requirements 
(assert (ite (> Location 0)  
     (and (= ConfPriority 0.8) (= AuthentPriority  0.8) (= IntegPriority 0.75) 
          (= EffectPriority 0.5) (= EfficPriority 0.55) (= PerformancePriority 0.57))  true )) 

;; The impact of the unusual time on the requirements
(assert (ite (> UnusualTime 0)
     (and (>= ConfPriority 0.6) (>= AuthentPriority  0.7) (>= IntegPriority 0.5) 
          (= EffectPriority 0.5) (>= EfficPriority 0.5) (= PerformancePriority 0.57)) true ))
             

;; The impact of the assets and operations on the priority of the security requirements
(assert (ite (and (> Controlled 0) (> NonControlled 0) (> TreatmentPlan 0))
             (and (>= ConfPriority 0.8) (>= AuthentPriority 0.8) (>= IntegPriority 0.7) )
             true))

(assert (ite (and (= Controlled 0) (> NonControlled 0) (> TreatmentPlan 0))
             (and (>= ConfPriority 0.7) (>= AuthentPriority 0.8) (>= IntegPriority 0.65) )
             true))

(assert (ite (and (= Controlled 0) (> NonControlled 0) (= TreatmentPlan 0))
             (and (>= ConfPriority 0.6) (>= AuthentPriority 0.8) (>= IntegPriority 0.6) )
             true))

;;  If (> NightTime 0) ( (= Iris 0)& (= Face  0) )                   
(assert (ite (> NightTime 0)  (and (= Iris 0) (= Face  0) ) true ))   


;;--------------------------------

;;I added a new equation for the satisfaction calculation 
;; Confidentiality= (AvgConfidentiality * ConfPriority)
;; Implement Confidentiality = AvgConfidentiality - max(0, ConfPriority - AvgConfidentiality)
(assert (= Confidentiality (ite (>= AvgConfidentiality ConfPriority) (* AvgConfidentiality ConfPriority)
          (- AvgConfidentiality (/ (* (- ConfPriority AvgConfidentiality) (- ConfPriority AvgConfidentiality)) ConfPriority)))))

(assert (= Integrity (ite (>= AvgIntegrity IntegPriority) (* AvgIntegrity IntegPriority)
          (- AvgIntegrity (/ (* (- IntegPriority AvgIntegrity) (- IntegPriority AvgIntegrity)) IntegPriority)))))

(assert (= Authenticity (ite (>= AvgAuthenticity AuthentPriority) (* AvgAuthenticity AuthentPriority)
          (- AvgAuthenticity (/ (* (- AuthentPriority AvgAuthenticity)
                                   (- AuthentPriority AvgAuthenticity))
                                 AuthentPriority)))))

(assert (= Efficiency (ite (>= AvgEfficiency EfficPriority) (* AvgEfficiency EfficPriority)
          (- AvgEfficiency (/ (* (- EfficPriority AvgEfficiency) (- EfficPriority AvgEfficiency)) EfficPriority)))))

(assert (= Effectiveness (ite (>= AvgEffectiveness EffectPriority) (* AvgEffectiveness EffectPriority)
          (- AvgEffectiveness (/ (* (- EffectPriority AvgEffectiveness) (- EffectPriority AvgEffectiveness)) EffectPriority)))))

(assert (= Performance (ite (>= AvgPerformance PerformancePriority) (* AvgPerformance PerformancePriority)
          (- AvgPerformance (/ (* (- PerformancePriority AvgPerformance) (- PerformancePriority AvgPerformance)) PerformancePriority)))))

;;;;Attacks
;; I have added the Risk before the mitigation as BPRisk
(declare-fun PImpersAttack() Real)
(declare-fun FPImpersAttack() Real)
(declare-fun PRiskPImpersAttack() Real )
(declare-fun BPRiskPImpersAttack() Real )

(assert (and (<= 0 PImpersAttack ) (<= PImpersAttack 1)))
(assert (and (<= 0 FPImpersAttack ) (<= FPImpersAttack 1)))
(assert (and (<= 0 PRiskPImpersAttack ) (<= PRiskPImpersAttack 1)))
(assert (and (<= 0 BPRiskPImpersAttack ) (<= BPRiskPImpersAttack 1)))

(declare-fun PReplayAttack() Real)
(declare-fun FPReplayAttack() Real)
(declare-fun PRiskReplayAttack() Real)
(declare-fun BPRiskReplayAttack() Real)

(assert (and (<= 0 PReplayAttack ) (<= PReplayAttack 1)))
(assert (and (<= 0 FPReplayAttack ) (<= FPReplayAttack 1)))
(assert (and (<= 0 PRiskReplayAttack ) (<= PRiskReplayAttack 1)))
(assert (and (<= 0 BPRiskReplayAttack ) (<= BPRiskReplayAttack 1)))


;;Session Hijacking attack
(declare-fun PSessionAttack() Real)
(declare-fun FPSessionAttack() Real)
(declare-fun PRiskSessionAttack() Real)
(declare-fun BPRiskSessionAttack() Real)

(assert (and (<= 0 PSessionAttack ) (<= PSessionAttack 1)))
(assert (and (<= 0 FPSessionAttack ) (<= FPSessionAttack 1)))
(assert (and (< 0 PRiskSessionAttack ) (<= PRiskSessionAttack 1)))
(assert (and (<= 0 PRiskSessionAttack ) (<= PRiskSessionAttack 1)))


; If(> Insecure Network 0)                
(assert (ite (> InsecNetwork 0) (and (= PImpersAttack 0.75) (= PSessionAttack 0.82) (= PReplayAttack 0.8) ) true  )) 


;; -----------Consider this section after the authentication-------------
(declare-fun  ImpersAttackImpact () Real) 
(declare-fun  ReplayAttackImpact () Real) 
(declare-fun  SessionAttackImpact () Real) 

(assert (and (<= 0 ImpersAttackImpact ) (<= ImpersAttackImpact 1)))
(assert (and (<= 0 ReplayAttackImpact ) (<= ReplayAttackImpact 1)))
(assert (and (<= 0 SessionAttackImpact ) (<= SessionAttackImpact 1)))


(declare-fun  ResRisk () Real)

;; Total Risk before any Mitigation
(declare-fun  TotalRisk () Real)

(assert (and (<= 0 ResRisk ) (<= ResRisk 1)))
(assert (and (<= 0 TotalRisk ) (<= TotalRisk 1)))

; Should I make the impact between 0 and 1 ??
;I change it from <= to = because these values should be fixed
;; AVG (authentication methods impact on the PImpersAttack psitive (0.5) very positively (0.8) , negative (0.3), very negative(0.1) and not impact (0)       
;; Dempster-Shafer combination function



;; The average maybe is not suitable here (maybe it's suitable because the first method can be vulnerable to this attack and the other method can be more vulenrable to another attack

(assert (<= ImpersAttackImpact (/ (+ (* PinLeng 0.3)
                               (* PassStr 0.3)
                               (* OtpLeng 0.3) 
                               (* Certificate 0.7)
                               (* SmartCard 0.3)
                               (* Token 0.3)
                               (* SignCryp 0.1)
                               (* GroupSign 0.1)
                               (* RingSign 0.1)
                               (* Iris 0.1)
                               (* Face 0.1)
                               (* Fingerprint 0.1) (ite (> TwoFactor 0) 0.3 0) ) count )
                                  )) 



;;PPImpersAttack=(PkPImpersAttack - ImpersAttackImpact)
(assert (=  FPImpersAttack (- PImpersAttack ImpersAttackImpact )))

;; AVG (authentication methods impact on the PImpersAttack psitive (0.5) very positively (0.8) , negative (0.3), very negative(0.1) and not impact (0)                          
(assert (<= ReplayAttackImpact (/ (+ (* PinLeng 0.3)
                               (* PassStr 0.3)
                               (* OtpLeng 0.1) 
                               (* Certificate 0.7)
                               (* SmartCard 0.3)
                               (* Token 0.1)
                               (* SignCryp 0.1)
                               (* GroupSign 0.1)
                               (* RingSign 0.1)
                               (* Iris 0.1)
                               (* Face 0.1)
                               (* Fingerprint 0.1) (ite (> TwoFactor 0) 0.3 0) ) count )
                                  ))  


;;Final PReplayAttack  =(PReplayAttack - ReplayAttackImpact )
(assert (= FPReplayAttack (- PReplayAttack ReplayAttackImpact )))


;; AVG (authentication methods impact on the PImpersAttack psitive (0.5) very positively (0.8) , negative (0.3), very negative(0.1) and not impact (0)                          
(assert (<= SessionAttackImpact (/ (+ (* PinLeng 0.3)
                               (* PassStr 0.3)
                               (* OtpLeng 0.3) 
                               (* Certificate 0.5)
                               (* SmartCard 0.6)
                               (* Token 0.6)
                               (* SignCryp 0.2)
                               (* GroupSign 0.2)
                               (* RingSign 0.2)
                               (* Iris 0.3)
                               (* Face 0.3)
                               (* Fingerprint 0.3) (ite (> TwoFactor 0) 0.3 0) )) true )
                                  )

;;Final FPSessionAttack  =(PSessionAttack - SessionAttackImpact )
(assert (= FPSessionAttack (- PSessionAttack SessionAttackImpact )))


;;Risk of the attacks before the mitigation 
(assert (= BPRiskPImpersAttack (* PImpersAttack AssetValue) ) )
(assert (= BPRiskReplayAttack (* PReplayAttack AssetValue) ) )
(assert (= BPRiskSessionAttack (* PSessionAttack AssetValue) ) )

;; The Total Risk before any mitigation
(assert (= TotalRisk (ite (>= BPRiskPImpersAttack BPRiskReplayAttack)
                     (ite (>= BPRiskPImpersAttack BPRiskSessionAttack) BPRiskPImpersAttack BPRiskSessionAttack)
                     (ite (>= BPRiskReplayAttack BPRiskSessionAttack) BPRiskReplayAttack BPRiskSessionAttack))))


;;Risk of the attack = Probability of attack after mitigation * Asset value 
(assert (= PRiskPImpersAttack (* FPImpersAttack AssetValue) ) )
(assert (= PRiskReplayAttack (* FPReplayAttack AssetValue) ) )
(assert (= PRiskSessionAttack (* FPSessionAttack AssetValue) ) )

;;ResidualRisk = MAX(TotalRisk*(1 - Impact)  PRiskReplayAttack PRiskSessionAttack) 
(assert (= ResRisk (ite (>= PRiskPImpersAttack PRiskReplayAttack)
                     (ite (>= PRiskPImpersAttack PRiskSessionAttack) PRiskPImpersAttack PRiskSessionAttack)
                     (ite (>= PRiskReplayAttack PRiskSessionAttack) PRiskReplayAttack PRiskSessionAttack))))

;; Utility=AVG(Security  Usability Performance (- 1 ResidualRisk))
(assert (<= Utility (/ (+ Security  Usability Performance (- 1 ResRisk)) 4))) 

;; -------------------------------------  New Added Sections  -------------------------------------
;; Goals satisfacction
(declare-fun GoalSatisfaction () Real)
(assert (= GoalSatisfaction (/ (+ Security Usability Performance) 3)))

(declare-fun SessionTime () Real)
(declare-fun BehaviorDeviation () Real)

;; SessionTime: duration of the session (0 = short, 1 = long)
(assert (and (>= SessionTime 0) (<= SessionTime 1)))

;; BehaviorDeviation: deviation from the user’s typical behavior (0 = normal, 1 = highly unusual)
(assert (and (>= BehaviorDeviation 0) (<= BehaviorDeviation 1)))

;; SessionTime and BehaviorDeviation are contextual indicators that increase the likelihood
;; of session hijacking if the session is long or the user behaves unusually. These factors
;; dynamically raise PSessionAttack and can trigger stricter security requirements.

;Session hijacking becomes more likely with:
;Longer sessions (more time to attack)
;Unusual behavior (indicates a possible hijacker)
;; Adjust PSessionAttack based on context
;; Base = 0.8 from insecure network, but increase it further if the session is long and behavior is unusual

;;(assert (ite (> InsecNetwork 0)
 ;; (= PSessionAttack (+ 0.8 (* 0.1 SessionTime) (* 0.1 BehaviorDeviation)))  ; up to 1.0 max
  ;;(= PSessionAttack (+ 0.4 (* 0.3 SessionTime) (* 0.3 BehaviorDeviation)))  ; base is lower
;))

(assert (> Location 0))

(assert (> UnusualTime 0))

(assert (> InsecNetwork 0))


;;-----------------------Authorization Section-------------------------;;
;;Must have vs Nice to have vs Optional
(declare-fun Must () Real)
(declare-fun Nice () Real)
(declare-fun Optional () Real)

(assert (or (= 0 Must) (= Must 1)))
(assert (or (= 0 Nice) (= Nice 1)))
(assert (or (= 0 Optional) (= Optional 1)))


;; If an asset is ON, its Read permission must be ON.
;; If the asset is OFF, all permissions must be OFF.
(assert (ite (> Diagnosis 0)
             (= Diagnosis_Read true)
             (and (= Diagnosis_Read false)
                  (= Diagnosis_Write false)
                  (= Diagnosis_Update false)
                  (= Diagnosis_Delete false))))

(assert (ite (> TreatmentPlan 0)
             (= TreatmentPlan_Read true)
             (and (= TreatmentPlan_Read false)
                  (= TreatmentPlan_Write false)
                  (= TreatmentPlan_Update false)
                  (= TreatmentPlan_Delete false))))

(assert (ite (> LabResults 0)
             (= LabResults_Read true)
             (and (= LabResults_Read false)
                  (= LabResults_Write false)
                  (= LabResults_Update false)
                  (= LabResults_Delete false))))

(assert (ite (> TestReports 0)
             (= TestReports_Read true)
             (and (= TestReports_Read false)
                  (= TestReports_Write false)
                  (= TestReports_Update false)
                  (= TestReports_Delete false))))

(assert (ite (> NonControlledPrescriptions 0)
             (= NonControlledPrescriptions_Read true)
             (and (= NonControlledPrescriptions_Read false)
                  (= NonControlledPrescriptions_Write false)
                  (= NonControlledPrescriptions_Update false)
                  (= NonControlledPrescriptions_Delete false))))

(assert (ite (> PatientHistory 0)
             (= PatientHistory_Read true)
             (and (= PatientHistory_Read false)
                  (= PatientHistory_Write false)
                  (= PatientHistory_Update false)
                  (= PatientHistory_Delete false))))

(assert (ite (> ControlledPrescriptions 0)
             (= ControlledPrescriptions_Read true)
             (and (= ControlledPrescriptions_Read false)
                  (= ControlledPrescriptions_Write false)
                  (= ControlledPrescriptions_Update false)
                  (= ControlledPrescriptions_Delete false))))

(assert (ite (> PatientInteractions 0)
             (= PatientInteractions_Read true)
             (and (= PatientInteractions_Read false)
                  (= PatientInteractions_Write false)
                  (= PatientInteractions_Update false)
                  (= PatientInteractions_Delete false))))

(assert (ite (> VisitSummaries 0)
             (= VisitSummaries_Read true)
             (and (= VisitSummaries_Read false)
                  (= VisitSummaries_Write false)
                  (= VisitSummaries_Update false)
                  (= VisitSummaries_Delete false))))

(assert (ite (> ReferralNotes 0)
             (= ReferralNotes_Read true)
             (and (= ReferralNotes_Read false)
                  (= ReferralNotes_Write false)
                  (= ReferralNotes_Update false)
                  (= ReferralNotes_Delete false))))

(assert (ite (> EncounterNotes 0)
             (= EncounterNotes_Read true)
             (and (= EncounterNotes_Read false)
                  (= EncounterNotes_Write false)
                  (= EncounterNotes_Update false)
                  (= EncounterNotes_Delete false))))

(assert (ite (> PatientRecords 0)
             (= PatientRecords_Read true)
             (and (= PatientRecords_Read false)
                  (= PatientRecords_Write false)
                  (= PatientRecords_Update false)
                  (= PatientRecords_Delete false))))



;; Operations values
(assert (or (=  DiagnoseMedicalConditions 0) (= DiagnoseMedicalConditions 1)))
(assert (or (=  ViewLabResults 0) (= ViewLabResults 1)))
(assert (or (=  Controlled 0) (= Controlled 1)))
(assert (or (=  NonControlled 0) (= NonControlled 1)))
(assert (or (=  AddEncounterNote 0) (= AddEncounterNote 1)))
(assert (or (=  AddReferralNote 0) (= AddReferralNote 1)))
(assert (or (=  GenerateReports 0) (= GenerateReports 1)))

(assert (and (> Must 0) (> DiagnoseMedicalConditions 0) (> ViewLabResults 0)))

(assert (ite (or (> Controlled 0) (> NonControlled 0)) (> Nice 0) (= Nice 0)) )
(assert (ite (> Nice 0) (or (> Controlled 0) (> NonControlled 0)) (and (= Controlled 0) (= NonControlled 0)) ))

(assert  (ite (or (> AddEncounterNote 0) (> AddReferralNote 0) (> GenerateReports 0)) (> Optional 0) (= Optional 0)) )
(assert  (ite (> Optional 0) (or (> AddEncounterNote 0) (> AddReferralNote 0) (> GenerateReports 0)) (and (= AddEncounterNote 0) (= AddReferralNote 0) (= GenerateReports 0) )) )

(assert (or (> DiagnoseMedicalConditions 0) (> ViewLabResults 0 )
            (> Controlled 0) (> NonControlled 0) (> AddEncounterNote 0)
            (> AddReferralNote 0) (> GenerateReports 0)))



;; Apply the hierarchy to all assets
(assert (HierarchicalPermissions Diagnosis_Delete Diagnosis_Update Diagnosis_Write Diagnosis_Read))
(assert (HierarchicalPermissions TreatmentPlan_Delete TreatmentPlan_Update TreatmentPlan_Write TreatmentPlan_Read))
(assert (HierarchicalPermissions LabResults_Delete LabResults_Update LabResults_Write LabResults_Read))
(assert (HierarchicalPermissions TestReports_Delete TestReports_Update TestReports_Write TestReports_Read))
(assert (HierarchicalPermissions NonControlledPrescriptions_Delete NonControlledPrescriptions_Update NonControlledPrescriptions_Write NonControlledPrescriptions_Read))
(assert (HierarchicalPermissions PatientHistory_Delete PatientHistory_Update PatientHistory_Write PatientHistory_Read))
(assert (HierarchicalPermissions ControlledPrescriptions_Delete ControlledPrescriptions_Update ControlledPrescriptions_Write ControlledPrescriptions_Read))
(assert (HierarchicalPermissions PatientInteractions_Delete PatientInteractions_Update PatientInteractions_Write PatientInteractions_Read))
(assert (HierarchicalPermissions VisitSummaries_Delete VisitSummaries_Update VisitSummaries_Write VisitSummaries_Read))
(assert (HierarchicalPermissions ReferralNotes_Delete ReferralNotes_Update ReferralNotes_Write ReferralNotes_Read))
(assert (HierarchicalPermissions EncounterNotes_Delete EncounterNotes_Update EncounterNotes_Write EncounterNotes_Read))
(assert (HierarchicalPermissions PatientRecords_Delete PatientRecords_Update PatientRecords_Write PatientRecords_Read))
;; ------------------------------------------------------------------------------

;; If Read is false then higher levels must be false too
(define-fun Downclose ((D Bool) (U Bool) (W Bool) (R Bool)) Bool
  (and (=> (not R) (and (not W) (not U) (not D)))
       (=> (not W) (and (not U) (not D)))
       (=> (not U) (not D))))

(assert (Downclose Diagnosis_Delete Diagnosis_Update Diagnosis_Write Diagnosis_Read))
(assert (Downclose TreatmentPlan_Delete TreatmentPlan_Update TreatmentPlan_Write TreatmentPlan_Read))
(assert (Downclose LabResults_Delete LabResults_Update LabResults_Write LabResults_Read))
(assert (Downclose TestReports_Delete TestReports_Update TestReports_Write TestReports_Read))
(assert (Downclose NonControlledPrescriptions_Delete NonControlledPrescriptions_Update NonControlledPrescriptions_Write NonControlledPrescriptions_Read))
(assert (Downclose PatientHistory_Delete PatientHistory_Update PatientHistory_Write PatientHistory_Read))
(assert (Downclose ControlledPrescriptions_Delete ControlledPrescriptions_Update ControlledPrescriptions_Write ControlledPrescriptions_Read))
(assert (Downclose PatientInteractions_Delete PatientInteractions_Update PatientInteractions_Write PatientInteractions_Read))
(assert (Downclose VisitSummaries_Delete VisitSummaries_Update VisitSummaries_Write VisitSummaries_Read))
(assert (Downclose ReferralNotes_Delete ReferralNotes_Update ReferralNotes_Write ReferralNotes_Read))
(assert (Downclose EncounterNotes_Delete EncounterNotes_Update EncounterNotes_Write EncounterNotes_Read))
(assert (Downclose PatientRecords_Delete PatientRecords_Update PatientRecords_Write PatientRecords_Read))


;; ---------- Minimum permissions required for each operation ----------

;; helper: “operation active ⇒ required permission”
(define-fun NeedsRead  ((op Real) (p Bool)) Bool (=> (> op 0) p))
(define-fun NeedsWrite ((op Real) (p Bool)) Bool (=> (> op 0) p))

;; -------------------- MUST-HAVE --------------------
;; DiagnoseMedicalConditions ⇒ Read Diagnosis & TreatmentPlan
(assert (NeedsRead DiagnoseMedicalConditions Diagnosis_Read))
(assert (NeedsRead DiagnoseMedicalConditions TreatmentPlan_Read))

;; ViewLabResults ⇒ Read LabResults & TestReports
(assert (NeedsRead ViewLabResults LabResults_Read))
(assert (NeedsRead ViewLabResults TestReports_Read))

;; -------------------- NICE-TO-HAVE --------------------
;; Controlled ⇒ Read ControlledPrescriptions & PatientHistory
(assert (NeedsRead Controlled ControlledPrescriptions_Read))
(assert (NeedsRead Controlled PatientHistory_Read))

;; NonControlled ⇒ Read NonControlledPrescriptions & PatientHistory
(assert (NeedsRead NonControlled NonControlledPrescriptions_Read))
(assert (NeedsRead NonControlled PatientHistory_Read))

;; -------------------- OPTIONAL --------------------
;; AddEncounterNote ⇒ Write PatientInteractions & VisitSummaries  (Write ⇒ Read via hierarchy)
(assert (NeedsWrite AddEncounterNote PatientInteractions_Write))
(assert (NeedsWrite AddEncounterNote VisitSummaries_Write))

;; AddReferralNote ⇒ Write ReferralNotes & EncounterNotes
(assert (NeedsWrite AddReferralNote ReferralNotes_Write))
(assert (NeedsWrite AddReferralNote EncounterNotes_Write))

;; GenerateReports ⇒ Read Diagnosis, TreatmentPlan, LabResults, PatientRecords
(assert (NeedsRead GenerateReports Diagnosis_Read))
(assert (NeedsRead GenerateReports TreatmentPlan_Read))
(assert (NeedsRead GenerateReports LabResults_Read))
(assert (NeedsRead GenerateReports PatientRecords_Read))
;; --------------------------------------------------------------------

;; If the Optional is active then the Nice should be active
;all Optional OFF ?
(define-fun OptionalAllOff () Bool
  (and (= AddEncounterNote 0.0)
       (= AddReferralNote 0.0)
       (= GenerateReports 0.0)))

; Enforce: Nice can be OFF only after all Optional are OFF
(assert (=> (= Controlled 0.0)     OptionalAllOff))
(assert (=> (= NonControlled 0.0)  OptionalAllOff))

;; ==================== AUTHORIZATION PENALTY (fixed: Reals + names) ====================

;; Helpers with Real literals to avoid sort mismatch
(define-fun _min2 ((a Real) (b Real)) Real (ite (<= a b) a b))
(define-fun _max2 ((a Real) (b Real)) Real (ite (>= a b) a b))
(define-fun _clamp01 ((x Real)) Real (_min2 1.0 (_max2 0.0 x)))

;; Permission level (cumulative): Read=0, Write=1, Update=2, Delete=3
(define-fun _lvlcost ((D Bool) (U Bool) (W Bool) (R Bool)) Real
  (ite D 3.0 (ite U 2.0 (ite W 1.0 (ite R 0.0 0.0)))))

;; “Reduction tightness” used as a penalty when you LOWER permissions:
;; Read=1.0, Write=2/3, Update=1/3, Delete=0.0
(define-fun _tight ((D Bool) (U Bool) (W Bool) (R Bool)) Real
  (- 1.0 (/ (_lvlcost D U W R) 3.0)))

;; -------- Permission penalty (↑ when permissions are REDUCED; 0 if asset OFF) --------
(declare-fun PermPenalty () Real)
(assert (= PermPenalty
  (+ (* (_tight Diagnosis_Delete Diagnosis_Update Diagnosis_Write Diagnosis_Read)                             DiagnosisSensitivity Diagnosis)
     (* (_tight TreatmentPlan_Delete TreatmentPlan_Update TreatmentPlan_Write TreatmentPlan_Read)             TreatmentPlanSensitivity TreatmentPlan)
     (* (_tight LabResults_Delete LabResults_Update LabResults_Write LabResults_Read)                         LabResultsSensitivity LabResults)
     (* (_tight TestReports_Delete TestReports_Update TestReports_Write TestReports_Read)                     TestReportsSensitivity TestReports)
     (* (_tight NonControlledPrescriptions_Delete NonControlledPrescriptions_Update NonControlledPrescriptions_Write NonControlledPrescriptions_Read) NonControlledPrescriptionsSensitivity NonControlledPrescriptions)
     (* (_tight PatientHistory_Delete PatientHistory_Update PatientHistory_Write PatientHistory_Read)          PatientHistorySensitivity PatientHistory)
     (* (_tight ControlledPrescriptions_Delete ControlledPrescriptions_Update ControlledPrescriptions_Write ControlledPrescriptions_Read) ControlledPrescriptionsSensitivity ControlledPrescriptions)
     (* (_tight PatientInteractions_Delete PatientInteractions_Update PatientInteractions_Write PatientInteractions_Read) PatientInteractionsSensitivity PatientInteractions)
     (* (_tight VisitSummaries_Delete VisitSummaries_Update VisitSummaries_Write VisitSummaries_Read)         VisitSummariesSensitivity VisitSummaries)
     (* (_tight ReferralNotes_Delete ReferralNotes_Update ReferralNotes_Write ReferralNotes_Read)             ReferralNotesSensitivity ReferralNotes)
     (* (_tight EncounterNotes_Delete EncounterNotes_Update EncounterNotes_Write EncounterNotes_Read)         EncounterNotesSensitivity EncounterNotes)
     (* (_tight PatientRecords_Delete PatientRecords_Update PatientRecords_Write PatientRecords_Read)         PatientRecordsSensitivity PatientRecords)
  )))
(declare-fun PermPenaltyN () Real)
(assert (= PermPenaltyN (_clamp01 (/ PermPenalty 12.0))))  ;; 12 assets max

;; -------- Operation penalty (↑ when operations are DISABLED) --------
;; op=1.0 (enabled) => 0; op=0.0 (disabled) => positive penalty. Tune weights as needed.
(declare-fun OpDisabledPenalty () Real)
(assert (= OpDisabledPenalty
  (+ (* 1.0 (- 1.0 DiagnoseMedicalConditions))  ;; Must
     (* 1.0 (- 1.0 ViewLabResults))            ;; Must
     (* 0.7 (- 1.0 Controlled))                ;; Nice
     (* 0.7 (- 1.0 NonControlled))             ;; Nice
     (* 0.4 (- 1.0 AddEncounterNote))          ;; Optional
     (* 0.4 (- 1.0 AddReferralNote))           ;; Optional
     (* 0.4 (- 1.0 GenerateReports))           ;; Optional
  )))
(declare-fun OpDisabledPenaltyN () Real)
(assert (= OpDisabledPenaltyN (_clamp01 (/ OpDisabledPenalty 4.9))))  ;; 4.1 = 1+1+0.6+0.6+0.3+0.3+0.3

;; -------- Combined penalty: higher when ops are DISABLED and perms are REDUCED --------
(declare-fun AuthorizationPenalty () Real)
(assert (= AuthorizationPenalty
  (_clamp01
    (+ (* 0.6 PermPenaltyN)       ;; penalty for reduced permissions
       (* 0.9 OpDisabledPenaltyN) ;; penalty for disabled operations
    ))))
(assert (and (>= AuthorizationPenalty 0.0) (<= AuthorizationPenalty 1.0)))
;; ==================== END AUTHORIZATION PENALTY ====================

(declare-fun Alpha () Real)
(declare-fun Beta () Real)
(assert (and (>= Alpha 0.0) (>= Beta 0.0) (= (+ Alpha Beta) 1.0)))
(declare-fun AuthUtility () Real)


(assert (= AuthUtility (/ (+ (- 1.0 ResRisk)
                           AssetValue ) 2)
                          ))


(check-sat)
(get-model)