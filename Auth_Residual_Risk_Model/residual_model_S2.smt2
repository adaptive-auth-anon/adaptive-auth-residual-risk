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

;; The forth scenario contextual factors
(declare-fun Location() Real)
(declare-fun UnsecuredWiFi() Real)
(declare-fun InsecNetwork() Real)
(declare-fun Emergency() Real)
(declare-fun UnknownDevice() Real)
(declare-fun PoorLighting () Real)

;; 0 positive and 1 negative
(assert (or (=  Location 0) (= Location 1)))
(assert (or (=  UnsecuredWiFi 0) (= UnsecuredWiFi 1)))
(assert (or (=  InsecNetwork 0) (= InsecNetwork 1)))
(assert (or (=  Emergency 0) (= Emergency 1)))
(assert (or (=  UnknownDevice 0) (= UnknownDevice 1)))
(assert (or (=  PoorLighting 0) (= PoorLighting 1)))



;; Operation Declarations
(declare-fun AccessPatientProfile () Real)
(declare-fun OrderLabTest () Real)
(declare-fun ViewRadiologyImages () Real)
(declare-fun ApproveDischargeSummary () Real)
(declare-fun AdjustCarePlan () Real)
(declare-fun RequestConsultation () Real)
(declare-fun ManageAppointment () Real)
(declare-fun CommunicateWithPatient () Real)
(declare-fun PrintMedicalReport () Real)


;; Operations values 
(assert (or (= AccessPatientProfile 0) (= AccessPatientProfile 1)))
(assert (or (= OrderLabTest 0) (= OrderLabTest 1)))
(assert (or (= ViewRadiologyImages 0) (= ViewRadiologyImages 1)))
(assert (or (= ApproveDischargeSummary 0) (= ApproveDischargeSummary 1)))
(assert (or (= AdjustCarePlan 0) (= AdjustCarePlan 1)))
(assert (or (= RequestConsultation 0) (= RequestConsultation 1)))
(assert (or (= ManageAppointment 0) (= ManageAppointment 1)))
(assert (or (= CommunicateWithPatient 0) (= CommunicateWithPatient 1)))
(assert (or (= PrintMedicalReport 0) (= PrintMedicalReport 1)))


;; Asset Declarations
(declare-fun Diagnosis () Real)
(declare-fun TreatmentPlan () Real)
(declare-fun LabResults () Real)
(declare-fun TestReports () Real)
(declare-fun PatientHistory () Real)
(declare-fun PatientInteractions () Real)
(declare-fun VisitSummaries () Real)
(declare-fun ReferralNotes () Real)
(declare-fun EncounterNotes () Real)
(declare-fun PatientRecords () Real)
(declare-fun PatientDemographics () Real)
(declare-fun RadiologyImages () Real)
(declare-fun DischargeSummaries () Real)
(declare-fun PatientCommunications () Real)



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

;; PatientInteractions
(declare-fun PatientInteractions_Read () Bool)
(declare-fun PatientInteractions_Write () Bool)
(declare-fun PatientInteractions_Update () Bool)
(declare-fun PatientInteractions_Delete () Bool)
(declare-fun PatientInteractionsSensitivity () Real)
(assert
  (ite PatientInteractions_Delete
    (and (>= PatientInteractionsSensitivity 0.87) (<= PatientInteractionsSensitivity 0.9))
    (ite PatientInteractions_Update
      (and (>= PatientInteractionsSensitivity 0.84) (<= PatientInteractionsSensitivity 0.87))
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
    (and (>= PatientRecordsSensitivity 0.97) (<= PatientRecordsSensitivity 0.99))
    (ite PatientRecords_Update
      (and (>= PatientRecordsSensitivity 0.94) (<= PatientRecordsSensitivity 0.97))
      (ite PatientRecords_Write
        (and (>= PatientRecordsSensitivity 0.92) (<= PatientRecordsSensitivity 0.94))
        (and (>= PatientRecordsSensitivity 0.9) (<= PatientRecordsSensitivity 0.92))
      )
    )
  )
)




;; PatientDemographics Sensitivity and Permissions
(declare-fun PatientDemographics_Read () Bool)
(declare-fun PatientDemographics_Write () Bool)
(declare-fun PatientDemographics_Update () Bool)
(declare-fun PatientDemographics_Delete () Bool)
(declare-fun PatientDemographicsSensitivity () Real)

(assert
  (ite PatientDemographics_Delete
    (and (>= PatientDemographicsSensitivity 0.7) (<= PatientDemographicsSensitivity 0.75))
    (ite PatientDemographics_Update
      (and (>= PatientDemographicsSensitivity 0.65) (<= PatientDemographicsSensitivity 0.7))
      (ite PatientDemographics_Write
        (and (>= PatientDemographicsSensitivity 0.6) (<= PatientDemographicsSensitivity 0.65))
        (and (>= PatientDemographicsSensitivity 0.5) (<= PatientDemographicsSensitivity 0.6))
      )
    )
  )
)

;; RadiologyImages
(declare-fun RadiologyImages_Read () Bool)
(declare-fun RadiologyImages_Write () Bool)
(declare-fun RadiologyImages_Update () Bool)
(declare-fun RadiologyImages_Delete () Bool)
(declare-fun RadiologyImagesSensitivity () Real)

(assert
  (ite RadiologyImages_Delete
    (and (>= RadiologyImagesSensitivity 0.85) (<= RadiologyImagesSensitivity 0.9))
    (ite RadiologyImages_Update
      (and (>= RadiologyImagesSensitivity 0.8) (<= RadiologyImagesSensitivity 0.85))
      (ite RadiologyImages_Write
        (and (>= RadiologyImagesSensitivity 0.77) (<= RadiologyImagesSensitivity 0.8))
        (and (>= RadiologyImagesSensitivity 0.75) (<= RadiologyImagesSensitivity 0.77))
      )
    )
  )
)

;; DischargeSummary
(declare-fun DischargeSummaries_Read () Bool)
(declare-fun DischargeSummaries_Write () Bool)
(declare-fun DischargeSummaries_Update () Bool)
(declare-fun DischargeSummaries_Delete () Bool)
(declare-fun DischargeSummariesSensitivity () Real)

(assert
  (ite DischargeSummaries_Delete
    (and (>= DischargeSummariesSensitivity 0.8) (<= DischargeSummariesSensitivity 0.83))
    (ite DischargeSummaries_Update
      (and (>= DischargeSummariesSensitivity 0.78) (<= DischargeSummariesSensitivity 0.83))
      (ite DischargeSummaries_Write
        (and (>= DischargeSummariesSensitivity 0.73) (<= DischargeSummariesSensitivity 0.78))
        (and (>= DischargeSummariesSensitivity 0.65) (<= DischargeSummariesSensitivity 0.73))
      )
    )
  )
)



;; PatientCommunications
(declare-fun PatientCommunications_Read () Bool)
(declare-fun PatientCommunications_Write () Bool)
(declare-fun PatientCommunications_Update () Bool)
(declare-fun PatientCommunications_Delete () Bool)
(declare-fun PatientCommunicationsSensitivity () Real)

(assert
  (ite PatientCommunications_Delete
    (and (>= PatientCommunicationsSensitivity 0.65) (<= PatientCommunicationsSensitivity 0.68))
    (ite PatientCommunications_Update
      (and (>= PatientCommunicationsSensitivity 0.61) (<= PatientCommunicationsSensitivity 0.65))
      (ite PatientCommunications_Write
        (and (>= PatientCommunicationsSensitivity 0.55) (<= PatientCommunicationsSensitivity 0.61))
        (and (>= PatientCommunicationsSensitivity 0.5) (<= PatientCommunicationsSensitivity 0.55))
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


;; Needs adjustment
;; Asset value is >= 0 and <= 1
(assert (or (=  Diagnosis 0) (= Diagnosis 1)))
(assert (ite (or (> AdjustCarePlan 0) (> PrintMedicalReport 0) )(> Diagnosis 0)(= Diagnosis 0) ))

(assert (or (=  PatientRecords 0) (= PatientRecords 1)))
(assert (ite (or (> AccessPatientProfile 0) (> ViewRadiologyImages 0) (> ManageAppointment 0) (> PrintMedicalReport 0))(> PatientRecords 0)(= PatientRecords 0) ))

(assert (or (=  TreatmentPlan 0) (= TreatmentPlan 1)))
(assert (ite (or (> ApproveDischargeSummary 0) (> AdjustCarePlan 0) (> PrintMedicalReport 0))(> TreatmentPlan 0)(= TreatmentPlan 0) ))

(assert (or (=  LabResults 0) (= LabResults 1)))
(assert (ite (> OrderLabTest 0) (> LabResults 0)(= LabResults 0) ))

(assert (or (=  TestReports 0) (= TestReports 1)))
(assert (ite ( or (> OrderLabTest 0) (> ViewRadiologyImages 0)) (> TestReports 0) (= TestReports 0) ))

(assert (or (=  PatientHistory 0) (= PatientHistory 1)))
(assert (ite (> AccessPatientProfile 0) (> PatientHistory 0)(= PatientHistory 0) ))

(assert (or (=  PatientInteractions 0) (= PatientInteractions 1)))
(assert (ite (> CommunicateWithPatient 0) (> PatientInteractions 0) (= PatientInteractions 0) ))

(assert (or (=  VisitSummaries 0) (= VisitSummaries 1)))
(assert (ite (or (> ApproveDischargeSummary 0) (> ManageAppointment 0))(> VisitSummaries 0)(= VisitSummaries 0) ))


(assert (or (=  ReferralNotes 0) (= ReferralNotes 1)))
(assert (ite (> RequestConsultation 0) (> ReferralNotes 0) (= ReferralNotes 0) ))

(assert (or (=  EncounterNotes 0) (= EncounterNotes 1)))
(assert (ite (> RequestConsultation 0) (> EncounterNotes 0) (= EncounterNotes 0) ))

(assert (or (=  PatientDemographics 0) (= PatientDemographics 1)))
(assert (ite (> AccessPatientProfile 0) (> PatientDemographics 0) (= PatientDemographics 0) ))

(assert (or (=  RadiologyImages 0) (= RadiologyImages 1)))
(assert (ite (> ViewRadiologyImages 0) (> RadiologyImages 0) (= RadiologyImages 0) ))

(assert (or (=  DischargeSummaries 0) (= DischargeSummaries 1)))
(assert (ite (> ApproveDischargeSummary 0) (> DischargeSummaries 0) (= DischargeSummaries 0) ))

(assert (or (=  PatientCommunications 0) (= PatientCommunications 1)))
(assert (ite (> CommunicateWithPatient 0) (> PatientCommunications 0) (= PatientCommunications 0) ))

;;---------------------

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
(assert (or (= count 1) (= count 2)))

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

;-------------------------- Turning Off unsuitable authentication methods-----------------
(assert (= Token 0 ))
(assert (= SignCryp 0 ))
(assert (= Certificate 0 ))
(assert (= GroupSign 0 ))
(assert (= RingSign 0 ))

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
(assert (ite (> TwoFactor 0) (= AVGEfficSum (- (/ EfficSum  count) 0.1)) (= AVGEfficSum (/ EfficSum  count)) ))
 
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
(assert (ite (> TwoFactor 0) (= AVGEffetSum (- (/ EffetSum  count) 0.1) ) (= AVGEffetSum (/ EffetSum  count)) ))

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
(assert (ite (> TwoFactor 0) (= AVGPerforSum (- (/ PerforSum  count) 0.1)) (= AVGPerforSum PerforSum  ) ))

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
  (+ (* Diagnosis DiagnosisSensitivity 0.12)
     (* TreatmentPlan TreatmentPlanSensitivity 0.12)
     (* LabResults LabResultsSensitivity 0.08)
     (* TestReports TestReportsSensitivity 0.06)
     (* PatientHistory PatientHistorySensitivity 0.1)
     (* PatientInteractions PatientInteractionsSensitivity 0.05)
     (* VisitSummaries VisitSummariesSensitivity 0.05)
     (* ReferralNotes ReferralNotesSensitivity 0.05)
     (* EncounterNotes EncounterNotesSensitivity 0.05)
     (* PatientRecords PatientRecordsSensitivity 0.12)
     (* PatientDemographics PatientDemographicsSensitivity 0.05)
     (* RadiologyImages RadiologyImagesSensitivity 0.06)
     (* DischargeSummaries DischargeSummariesSensitivity 0.06)
     (* PatientCommunications PatientCommunicationsSensitivity 0.03))
))




;;---------------------------------
;;;; The contextual factors impact on the requirements priority

;; The impact of the unfamiliar location on the requirements
(assert (ite (> Location 0)  
     (and 
        (>= ConfPriority 0.7)         ;; Location can increase confidentiality priority
        (= AuthentPriority  0.7)      ;; Unusual location may suggest impersonation attempt — raises authenticity priority
        (>= IntegPriority 0.7)        ;; Data might be modified 
        (>= EffectPriority 0.6)        ;; Slight usability concern 
        (>= EfficPriority 0.7)         ;; 
        (> PerformancePriority 0.6))  ;; Slight impact 
      true )) 

;; The impact of unusual time on the requirements
(assert (ite (> Emergency 0)
     (and 
        (>= ConfPriority 0.6)         ;; Late hours can expose data if attacker exploits time gaps — confidentiality raised
        (>= AuthentPriority  0.7)     ;; Abnormal access time suggests possible impersonation — authenticity rises
        (>= IntegPriority 0.5)        ;; Risk of unintended changes at odd hours
        (= EffectPriority 0.7)        ;; Slight 
        (>= EfficPriority 0.75)        ;; 
        (>= PerformancePriority 0.75))  ;; 
      true ))

;; The impact of unknown device on the requirements
(assert (ite (> UnknownDevice 0)
  (and
    (>= ConfPriority 0.7)            ;; Personal or unmanaged devices are prone to data leakage — confidentiality is critical
    (>= AuthentPriority 0.7)          ;; Device unfamiliarity raises impersonation risk
    (>= IntegPriority 0.65)           ;; Integrity of submitted/modified data may be questioned
    (>= EffectPriority 0.7)           ;; Potential usability impact 
    (= EfficPriority 0.75)            ;; Effort increased for verification on new device
    (= PerformancePriority 0.5))      ;; May slow access due to additional checks 
  true))

;; The impact of unsecured WiFi on the authentication requirements
(assert (ite (> UnsecuredWiFi 0)
     (and 
          (= ConfPriority 0.7)       ;; MITM attacks more likely — confidentiality at high risk
          (>= AuthentPriority 0.7)    ;; Session hijacking or spoofing possible — higher authenticity needed
          (>= IntegPriority 0.65)      ;; Data integrity during transmission may be compromised
          (= EffectPriority 0.7)      ;; Slight usability impact from fallback to safer methods
          (= EfficPriority 0.75)      ;; 
          (> PerformancePriority 0.6) ;; 
     ) 
  true))


;;  If (> NightTime 0) ( (= Iris 0)& (= Face  0) )                   
(assert (ite (> PoorLighting 0)  (and (= Iris 0) (= Face  0) ) true ))   


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
(assert (and (< 0 PRiskPImpersAttack ) (<= PRiskPImpersAttack 1)))
(assert (and (<= 0 BPRiskPImpersAttack ) (<= BPRiskPImpersAttack 1)))

(declare-fun PReplayAttack() Real)
(declare-fun FPReplayAttack() Real)
(declare-fun PRiskReplayAttack() Real)
(declare-fun BPRiskReplayAttack() Real)

(assert (and (<= 0 PReplayAttack ) (<= PReplayAttack 1)))
(assert (and (<= 0 FPReplayAttack ) (<= FPReplayAttack 1)))
(assert (and (< 0 PRiskReplayAttack ) (<= PRiskReplayAttack 1)))
(assert (and (<= 0 BPRiskReplayAttack ) (<= BPRiskReplayAttack 1)))


;;Session Hijacking attack
(declare-fun PSessionAttack() Real)
(declare-fun FPSessionAttack() Real)
(declare-fun PRiskSessionAttack() Real)
(declare-fun BPRiskSessionAttack() Real)

(assert (and (<= 0 PSessionAttack ) (<= PSessionAttack 1)))
(assert (and (<= 0 FPSessionAttack ) (<= FPSessionAttack 1)))
(assert (and (< 0 PRiskSessionAttack ) (<= PRiskSessionAttack 1)))
(assert (and (<= 0 BPRiskSessionAttack ) (<= BPRiskSessionAttack 1)))

;;---------- The Context Impact On Attacks Likelihood

;; Unsecured WiFi can be easily intercepted by attackers. Replay attacks are likely due to token reuse, 
;; and session hijacking is highly likely due to lack of encryption or protection.
(assert (ite (> UnsecuredWiFi 0)
  (and
    (>= PReplayAttack 0.7)       ;; Replay risk high: attacker may intercept and reuse tokens
    (>= PSessionAttack 0.6))     ;; Session hijacking very likely over open networks
  true))

;; Unknown Device may be compromised or lack trusted configurations.
;; High impersonation risk due to possible malware 
(assert (ite (> UnknownDevice 0)
  (and
    (>= PImpersAttack 0.75)      ;; Impersonation risk high: compromised or spoofed identity
    (>= PReplayAttack 0.6))      ;; Replay risk moderate: stored tokens may be reused
  true))

;; Unfamiliar Location implies deviation from normal patterns, suggesting a potential attacker.
;; Moderate to high impersonation and session hijacking risk due to context anomaly.
(assert (ite (> Location 0)
  (and
    (>= PImpersAttack 0.7)       ;; Impersonation risk moderate-high: user location is suspicious
    (< PSessionAttack 0.7))     ;; Session hijacking risk elevated: access from unknown place
  true))


;; The Malware Risk
(declare-fun MalwareRisk () Real)
(assert (and (>= MalwareRisk 0) (<= MalwareRisk 1)))

;; Unknown device implies higher malware risk
(assert (ite (> UnknownDevice 0)
  (>= MalwareRisk 0.7)  ;; Assume 70% likelihood when device is unknown
  (= MalwareRisk 0.3))) ;; Assume only 30% when device is known/trusted

;; Malware can elevate impersonation, replay, and session hijacking
(assert (ite (> MalwareRisk 0.3)
  (and
    (>= PImpersAttack 0.73)       ;; Impersonation risk moderate-high: user location is suspicious
    (>= PSessionAttack 0.77)     ;; Session hijacking risk elevated: access from unknown place
    (>= PReplayAttack 0.63))     ;; 
  true))
;(assert (>= PImpersAttack (+ PImpersAttack (* MalwareRisk 0.1))))     ;; 0.1 extra if malware present
;(assert (>= PReplayAttack (+ PReplayAttack (* MalwareRisk 0.1))))
;(assert (>= PSessionAttack (+ PSessionAttack (* MalwareRisk 0.15))))  ;; Session hijacking more sensitive







;; -----------Consider this section after the authentication-------------
(declare-fun  ImpersAttackImpact () Real) 
(declare-fun  ReplayAttackImpact () Real) 
(declare-fun  SessionAttackImpact () Real) 

(assert (and (<= 0 ImpersAttackImpact ) (<= ImpersAttackImpact 1)))
(assert (and (<= 0 ReplayAttackImpact ) (<= ReplayAttackImpact 1)))
(assert (and (< 0 SessionAttackImpact ) (<= SessionAttackImpact 1)))


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
(assert (<= SessionAttackImpact
  (/ (+ (* PinLeng 0.2)
        (* PassStr 0.2)
        (* OtpLeng 0.3)
        (* Certificate 0.5)
        (* SmartCard 0.6)
        (* Token 0.6)
        (* SignCryp 0.3)
        (* GroupSign 0.3)
        (* RingSign 0.3)
        (* Iris 0.3)
        (* Face 0.3)
        (* Fingerprint 0.3)
        (ite (> TwoFactor 0) 0.3 0))
     count)))

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

;(assert (ite (> InsecNetwork 0)
 ; (= PSessionAttack (+ 0.8 (* 0.1 SessionTime) (* 0.1 BehaviorDeviation)))  ; up to 1.0 max
  ;(= PSessionAttack (+ 0.4 (* 0.3 SessionTime) (* 0.3 BehaviorDeviation)))  ; base is lower
;))

;-------- S3 contextual factors ----------


(assert (> Location 0))
(assert (> Emergency 0))
(assert (= UnknownDevice 0))
(assert (> UnsecuredWiFi 0))


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


(assert (ite (> PatientHistory 0)
             (= PatientHistory_Read true)
             (and (= PatientHistory_Read false)
                  (= PatientHistory_Write false)
                  (= PatientHistory_Update false)
                  (= PatientHistory_Delete false))))

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

(assert (ite (> PatientDemographics 0)
             (= PatientDemographics_Read true)
             (and (= PatientDemographics_Read false)
                  (= PatientDemographics_Write false)
                  (= PatientDemographics_Update false)
                  (= PatientDemographics_Delete false))))

(assert (ite (> RadiologyImages 0)
             (= RadiologyImages_Read true)
             (and (= RadiologyImages_Read false)
                  (= RadiologyImages_Write false)
                  (= RadiologyImages_Update false)
                  (= RadiologyImages_Delete false))))


(assert (ite (> DischargeSummaries 0)
             (= DischargeSummaries_Read true)
             (and (= DischargeSummaries_Read false)
                  (= DischargeSummaries_Write false)
                  (= DischargeSummaries_Update false)
                  (= DischargeSummaries_Delete false))))

(assert (ite (> PatientCommunications 0)
             (= PatientCommunications_Read true)
             (and (= PatientCommunications_Read false)
                  (= PatientCommunications_Write false)
                  (= PatientCommunications_Update false)
                  (= PatientCommunications_Delete false))))

;; Operations values
(assert (or (= AccessPatientProfile 0) (= AccessPatientProfile 1)))
(assert (or (= OrderLabTest 0) (= OrderLabTest 1)))
(assert (or (= ViewRadiologyImages 0) (= ViewRadiologyImages 1)))
(assert (or (= ApproveDischargeSummary 0) (= ApproveDischargeSummary 1)))
(assert (or (= AdjustCarePlan 0) (= AdjustCarePlan 1)))
(assert (or (= RequestConsultation 0) (= RequestConsultation 1)))
(assert (or (= ManageAppointment 0) (= ManageAppointment 1)))
(assert (or (= CommunicateWithPatient 0) (= CommunicateWithPatient 1)))
(assert (or (= PrintMedicalReport 0) (= PrintMedicalReport 1)))

;; Must category logic
(assert (and (> Must 0) (> AccessPatientProfile 0) (> OrderLabTest 0) (> AdjustCarePlan 0)))

;; Nice category logic
(assert (ite (or (> ApproveDischargeSummary 0) (> RequestConsultation 0) (> CommunicateWithPatient 0)) (> Nice 0) (= Nice 0)) )
(assert (ite (> Nice 0) (or (> ApproveDischargeSummary 0) (> RequestConsultation 0) (> CommunicateWithPatient 0)) 
            (and (= ApproveDischargeSummary 0) (= RequestConsultation 0) (= CommunicateWithPatient 0)) ))

;; Optional category logic
(assert (ite (or (> ViewRadiologyImages 0) (> ManageAppointment 0) (> PrintMedicalReport 0)) (> Optional 0) (= Optional 0)) )
(assert (ite (> Optional 0) (or (> ViewRadiologyImages 0) (> ManageAppointment 0) (> PrintMedicalReport 0)) 
             (and (= ViewRadiologyImages 0) (= ManageAppointment 0) (= PrintMedicalReport 0)) ))

;; At least one operation should be active
(assert (or (> AccessPatientProfile 0) (> OrderLabTest 0) (> AdjustCarePlan 0)
            (> ApproveDischargeSummary 0) (> RequestConsultation 0) (> CommunicateWithPatient 0)
            (> ViewRadiologyImages 0) (> ManageAppointment 0) (> PrintMedicalReport 0)))




;; Apply the hierarchy to all assets
(assert (HierarchicalPermissions Diagnosis_Delete Diagnosis_Update Diagnosis_Write Diagnosis_Read))
(assert (HierarchicalPermissions TreatmentPlan_Delete TreatmentPlan_Update TreatmentPlan_Write TreatmentPlan_Read))
(assert (HierarchicalPermissions LabResults_Delete LabResults_Update LabResults_Write LabResults_Read))
(assert (HierarchicalPermissions TestReports_Delete TestReports_Update TestReports_Write TestReports_Read))
(assert (HierarchicalPermissions PatientHistory_Delete PatientHistory_Update PatientHistory_Write PatientHistory_Read))
(assert (HierarchicalPermissions PatientInteractions_Delete PatientInteractions_Update PatientInteractions_Write PatientInteractions_Read))
(assert (HierarchicalPermissions VisitSummaries_Delete VisitSummaries_Update VisitSummaries_Write VisitSummaries_Read))
(assert (HierarchicalPermissions ReferralNotes_Delete ReferralNotes_Update ReferralNotes_Write ReferralNotes_Read))
(assert (HierarchicalPermissions EncounterNotes_Delete EncounterNotes_Update EncounterNotes_Write EncounterNotes_Read))
(assert (HierarchicalPermissions PatientRecords_Delete PatientRecords_Update PatientRecords_Write PatientRecords_Read))
(assert (HierarchicalPermissions PatientDemographics_Delete PatientDemographics_Update PatientDemographics_Write PatientDemographics_Read))
(assert (HierarchicalPermissions RadiologyImages_Delete RadiologyImages_Update RadiologyImages_Write RadiologyImages_Read))
(assert (HierarchicalPermissions DischargeSummaries_Delete DischargeSummaries_Update DischargeSummaries_Write DischargeSummaries_Read))
(assert (HierarchicalPermissions PatientCommunications_Delete PatientCommunications_Update PatientCommunications_Write PatientCommunications_Read))



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
(assert (Downclose PatientHistory_Delete PatientHistory_Update PatientHistory_Write PatientHistory_Read))
(assert (Downclose PatientInteractions_Delete PatientInteractions_Update PatientInteractions_Write PatientInteractions_Read))
(assert (Downclose VisitSummaries_Delete VisitSummaries_Update VisitSummaries_Write VisitSummaries_Read))
(assert (Downclose ReferralNotes_Delete ReferralNotes_Update ReferralNotes_Write ReferralNotes_Read))
(assert (Downclose EncounterNotes_Delete EncounterNotes_Update EncounterNotes_Write EncounterNotes_Read))
(assert (Downclose PatientRecords_Delete PatientRecords_Update PatientRecords_Write PatientRecords_Read))
(assert (Downclose PatientDemographics_Delete PatientDemographics_Update PatientDemographics_Write PatientDemographics_Read))
(assert (Downclose RadiologyImages_Delete RadiologyImages_Update RadiologyImages_Write RadiologyImages_Read))
(assert (Downclose DischargeSummaries_Delete DischargeSummaries_Update DischargeSummaries_Write DischargeSummaries_Read))
(assert (Downclose PatientCommunications_Delete PatientCommunications_Update PatientCommunications_Write PatientCommunications_Read))


;; ---------- Minimum permissions required for each operation ----------

;; -------------------- MINIMUM PERMISSIONS (Scenario 4) --------------------

;; helper functions (reuse if already defined)
(define-fun NeedsRead  ((op Real) (p Bool)) Bool (=> (> op 0.0) p))
(define-fun NeedsWrite ((op Real) (p Bool)) Bool (=> (> op 0.0) p))
(define-fun NeedsUpdate ((op Real) (p Bool)) Bool (=> (> op 0.0) p))

;; AccessPatientProfile ⇒ Read PatientRecords, PatientDemographics, PatientHistory
(assert (NeedsRead AccessPatientProfile PatientRecords_Read))
(assert (NeedsRead AccessPatientProfile PatientDemographics_Read))
(assert (NeedsRead AccessPatientProfile PatientHistory_Read))

;; ViewRadiologyImages ⇒ Read RadiologyImages, TestReports, PatientRecords
(assert (NeedsRead ViewRadiologyImages RadiologyImages_Read))
(assert (NeedsRead ViewRadiologyImages TestReports_Read))
(assert (NeedsRead ViewRadiologyImages PatientRecords_Read))

;; ManageAppointment ⇒ Read PatientRecords, Write VisitSummaries
(assert (NeedsRead ManageAppointment PatientRecords_Read))
(assert (NeedsWrite ManageAppointment VisitSummaries_Write))

;; PrintMedicalReport ⇒ Read Diagnosis, TreatmentPlan, LabResults, PatientRecords, DischargeSummaries, PatientCommunications
(assert (NeedsRead PrintMedicalReport Diagnosis_Read))
(assert (NeedsRead PrintMedicalReport TreatmentPlan_Read))
(assert (NeedsRead PrintMedicalReport LabResults_Read))
(assert (NeedsRead PrintMedicalReport PatientRecords_Read))
(assert (NeedsRead PrintMedicalReport DischargeSummaries_Read))
(assert (NeedsRead PrintMedicalReport PatientCommunications_Read))

;; AdjustCarePlan ⇒ Update TreatmentPlan, Read Diagnosis, Read PatientRecords
(assert (NeedsUpdate AdjustCarePlan TreatmentPlan_Update))
(assert (NeedsRead AdjustCarePlan Diagnosis_Read))
(assert (NeedsRead AdjustCarePlan PatientRecords_Read))

;; ApproveDischargeSummary ⇒ Update DischargeSummaries, Read VisitSummaries, Read TreatmentPlan
(assert (NeedsUpdate ApproveDischargeSummary DischargeSummaries_Update))
(assert (NeedsRead ApproveDischargeSummary VisitSummaries_Read))
(assert (NeedsRead ApproveDischargeSummary TreatmentPlan_Read))

;; OrderLabTest ⇒ Write LabResults, Read TestReports, Read PatientRecords
(assert (NeedsWrite OrderLabTest LabResults_Write))
(assert (NeedsRead OrderLabTest TestReports_Read))
(assert (NeedsRead OrderLabTest PatientRecords_Read))

;; RequestConsultation ⇒ Write ReferralNotes, Write EncounterNotes, Read PatientRecords
(assert (NeedsWrite RequestConsultation ReferralNotes_Write))
(assert (NeedsWrite RequestConsultation EncounterNotes_Write))
(assert (NeedsRead RequestConsultation PatientRecords_Read))

;; CommunicateWithPatient ⇒ Write PatientCommunications, Read PatientInteractions
(assert (NeedsWrite CommunicateWithPatient PatientCommunications_Write))
(assert (NeedsRead CommunicateWithPatient PatientInteractions_Read))

;; --------------------------------------------------------------------

;; If the Optional is active then the Nice should be active
;all Optional OFF ?
(define-fun OptionalAllOff () Bool
  (and (= ViewRadiologyImages 0.0)
       (= ManageAppointment 0.0)
       (= PrintMedicalReport 0.0)))

; Enforce: Nice can be OFF only after all Optional are OFF
(assert (=> (= ApproveDischargeSummary 0.0)     OptionalAllOff))
(assert (=> (= RequestConsultation 0.0)  OptionalAllOff))
(assert (=> (= CommunicateWithPatient 0.0)  OptionalAllOff))

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
     (* (_tight PatientHistory_Delete PatientHistory_Update PatientHistory_Write PatientHistory_Read)          PatientHistorySensitivity PatientHistory)
     (* (_tight PatientInteractions_Delete PatientInteractions_Update PatientInteractions_Write PatientInteractions_Read) PatientInteractionsSensitivity PatientInteractions)
     (* (_tight VisitSummaries_Delete VisitSummaries_Update VisitSummaries_Write VisitSummaries_Read)         VisitSummariesSensitivity VisitSummaries)
     (* (_tight ReferralNotes_Delete ReferralNotes_Update ReferralNotes_Write ReferralNotes_Read)             ReferralNotesSensitivity ReferralNotes)
     (* (_tight EncounterNotes_Delete EncounterNotes_Update EncounterNotes_Write EncounterNotes_Read)         EncounterNotesSensitivity EncounterNotes)
     (* (_tight PatientRecords_Delete PatientRecords_Update PatientRecords_Write PatientRecords_Read)         PatientRecordsSensitivity PatientRecords)
     (* (_tight PatientDemographics_Delete PatientDemographics_Update PatientDemographics_Write PatientDemographics_Read)         PatientDemographicsSensitivity PatientDemographics)
     (* (_tight RadiologyImages_Delete RadiologyImages_Update RadiologyImages_Write RadiologyImages_Read)         RadiologyImagesSensitivity RadiologyImages)
     (* (_tight DischargeSummaries_Delete DischargeSummaries_Update DischargeSummaries_Write DischargeSummaries_Read)         DischargeSummariesSensitivity DischargeSummaries)
     (* (_tight PatientCommunications_Delete PatientCommunications_Update PatientCommunications_Write PatientCommunications_Read)         PatientCommunicationsSensitivity PatientCommunications)
  )))
(declare-fun PermPenaltyN () Real)
(assert (= PermPenaltyN (_clamp01 (/ PermPenalty 14.0))))  ;; 14 assets max

;; -------- Operation penalty (↑ when operations are DISABLED) --------
;; op=1.0 (enabled) => 0; op=0.0 (disabled) => positive penalty. Tune weights as needed.
(declare-fun OpDisabledPenalty () Real)
(assert (= OpDisabledPenalty
  (+ (* 1.0 (- 1.0 AccessPatientProfile))  ;; Must
     (* 1.0 (- 1.0 OrderLabTest))            ;; Must
     (* 1.0 (- 1.0 AdjustCarePlan))            ;; Must
     (* 0.7 (- 1.0 ApproveDischargeSummary))                ;; Nice
     (* 0.7 (- 1.0 RequestConsultation))                ;; Nice
     (* 0.7 (- 1.0 CommunicateWithPatient))             ;; Nice
     (* 0.4 (- 1.0 ViewRadiologyImages))          ;; Optional
     (* 0.4 (- 1.0 ManageAppointment))           ;; Optional
     (* 0.4 (- 1.0 PrintMedicalReport))           ;; Optional
  )))
(declare-fun OpDisabledPenaltyN () Real)
(assert (= OpDisabledPenaltyN (_clamp01 (/ OpDisabledPenalty 6.3))))  

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