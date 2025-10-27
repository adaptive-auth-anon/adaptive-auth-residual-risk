from z3 import *
import os
from fractions import Fraction

if os.path.exists("S1_runs_summary.csv"):
    os.remove("S1_runs_summary.csv")

# ---------------------------------
# Helpers
# ---------------------------------
def z3_to_python(val):
    """Convert a z3 value to a native Python value (bool/int/float/str)."""
    if val is None:
        return None
    if is_true(val):
        return True
    if is_false(val):
        return False
    if isinstance(val, IntNumRef):
        return int(val.as_long())
    if isinstance(val, RatNumRef):
        return float(val.numerator_as_long()) / float(val.denominator_as_long())
    if isinstance(val, AlgebraicNumRef):
        s = val.as_decimal(12)
        if s.endswith('?'):
            s = s[:-1]
        try:
            return float(s)
        except Exception:
            return s
    # RealNumRef sometimes shows as '1/2'
    s = str(val)
    try:
        if '/' in s:
            n, d = s.split('/')
            return float(n) / float(d)
        return float(s)
    except Exception:
        return s

def model_value(model, name, sort, default=None):
    """Evaluate symbol by name & sort in model."""
    sym = Const(name, sort)
    try:
        v = model.eval(sym, model_completion=True)
        return z3_to_python(v)
    except Exception:
        return default

def as_constraint(name, sort, truthy=True):
    """Constraint to fix a symbol to enabled/disabled using its sort."""
    k = sort.kind()
    if k == Z3_BOOL_SORT:
        return Bool(name) if truthy else Not(Bool(name))
    if k == Z3_INT_SORT:
        return (Int(name) > 0) if truthy else (Int(name) == 0)
    if k == Z3_REAL_SORT:
        return (Real(name) > 0) if truthy else (Real(name) == 0)
    return None

def fmt(x):
    if x is None:
        return "N/A"
    if isinstance(x, bool):
        return "1" if x else "0"
    if isinstance(x, int):
        return str(x)
    try:
        return f"{float(x):.6f}"
    except Exception:
        return str(x)

# ---------------------------------
# Shared names & mapping
# ---------------------------------
auth_methods = [
    "PinLeng", "PassStr", "OtpLeng", "Certificate", "SmartCard", "Token",
    "SignCryp", "GroupSign", "RingSign", "Iris", "Face", "Fingerprint"
]

assets = [
    "Diagnosis", "TreatmentPlan", "LabResults", "TestReports",
    "NonControlledPrescriptions", "PatientHistory", "ControlledPrescriptions",
    "PatientInteractions", "VisitSummaries", "ReferralNotes",
    "EncounterNotes", "PatientRecords"
]
ops = ["Read", "Write", "Update", "Delete"]

# Mirrors your SMT mapping
category_operations = {
    "Must": {
        "DiagnoseMedicalConditions": ["Diagnosis", "TreatmentPlan"],
        "ViewLabResults": ["LabResults", "TestReports"]
    },
    "Nice": {
        "Controlled": ["ControlledPrescriptions", "PatientHistory"],
        "NonControlled": ["NonControlledPrescriptions", "PatientHistory"]
    },
    "Optional": {
        "AddEncounterNote": ["PatientInteractions", "VisitSummaries"],
        "AddReferralNote": ["ReferralNotes", "EncounterNotes"],
        "GenerateReports": ["Diagnosis", "TreatmentPlan", "LabResults", "PatientRecords"]
    }
}

primary_keys = [
    "Security","Confidentiality","ConfPriority",
    "Authenticity","AuthentPriority","Integrity","IntegPriority",
    "Usability","Effectiveness","EffectPriority","Efficiency","EfficPriority",
    "Performance","AvgPerformance","PerformancePriority",
    "ResRisk","PImpersAttack","PSessionAttack","PReplayAttack",
    "TotalRisk","Utility","PRiskPImpersAttack","PRiskReplayAttack","PRiskSessionAttack",
    "AssetValue","TwoFactor",
    "Controlled","NonControlled","ViewLabResults","AddEncounterNote","AddReferralNote",
    "DiagnoseMedicalConditions","GenerateReports",
    "AuthorizationScore","Must","Nice","Optional"
]

# ---------------------------------
# Utility printers
# ---------------------------------
def print_operations_block(values, title="Operations"):
    print(title + ":")
    print("  "
          f"Controlled={fmt(values.get('Controlled'))} | "
          f"NonControlled={fmt(values.get('NonControlled'))} | "
          f"ViewLabResults={fmt(values.get('ViewLabResults'))} | "
          f"AddEncounterNote={fmt(values.get('AddEncounterNote'))} | "
          f"AddReferralNote={fmt(values.get('AddReferralNote'))} | "
          f"DiagnoseMedicalConditions={fmt(values.get('DiagnoseMedicalConditions'))} | "
          f"GenerateReports={fmt(values.get('GenerateReports'))}")

def get_permissions_for_asset(model, decls, asset_name):
    row = {}
    for o in ops:
        sym = f"{asset_name}_{o}"
        srt = decls.get(sym, BoolSort())
        row[o] = model_value(model, sym, srt)
    return row

def is_asset_on(model, decls, asset_name):
    """Check if asset variable is active (>0 or True)."""
    srt = decls.get(asset_name, RealSort())
    val = model_value(model, asset_name, srt)
    if isinstance(val, bool):
        return val
    if isinstance(val, (int, float)):
        return val > 0
    return False

def operation_is_active(model, decls, op_name):
    srt = decls.get(op_name, RealSort())
    val = model_value(model, op_name, srt)
    if isinstance(val, (int, float)):
        return val > 0
    if isinstance(val, bool):
        return val
    return False

def print_hierarchical_authorization(model, decls, title="Authorization Configuration"):
    print("\n" + title + ":")
    for category, ops_dict in category_operations.items():
        print(f"\n{category} Requirements:")
        for operation, linked_assets in ops_dict.items():
            active_op = operation_is_active(model, decls, operation)
            suffix = "" if active_op else " (inactive)"
            print(f"  Operation: {operation}{suffix}")
            # Always show the assets for this operation (even if inactive)
            for asset_name in linked_assets:
                perms = get_permissions_for_asset(model, decls, asset_name)
                r, w, u, d = [fmt(perms.get(x)) for x in ops]
                active_asset = is_asset_on(model, decls, asset_name)
                tag = "" if active_asset else "  [REMOVED]"
                print(f"    - {asset_name:25s}{tag}  R={r}  W={w}  U={u}  D={d}")

# --------- Minimal CSV logger ---------
import os, csv

LOG_PATH = "S1_runs_summary.csv"
CONFIG_COUNTER = {"n": 0}  # simple mutable counter

def _as_bool_zero(val):
    # treat None/"N/A" as Falsey; numbers <= 0 as False; booleans as is
    if val is None: return False
    if isinstance(val, bool): return val
    try:
        return float(val) > 0.0
    except Exception:
        return False

def _disabled_operations(model, decls):
    disabled = []
    for cat, ops_dict in category_operations.items():
        for op_name in ops_dict.keys():
            if not operation_is_active(model, decls, op_name):
                disabled.append(op_name)
    return disabled

def _removed_crud_by_asset(model, decls):
    rows = []
    for asset in assets:
        # removed asset (asset var off)
        on = is_asset_on(model, decls, asset)
        # CRUD flags
        perms = get_permissions_for_asset(model, decls, asset)
        removed = [crud for crud in ["Read","Write","Update","Delete"]
                   if not _as_bool_zero(perms.get(crud))]
        if (not on) or removed:
            rows.append(f"{asset}:" + ("REMOVED_ASSET" if not on else "") +
                        ("" if not on or not removed else "|") +
                        (",".join(removed) if removed else ""))
    return ";".join(rows)

def _get(model, decls, name, default=None):
    return model_value(model, name, decls.get(name, RealSort()), default)

def log_config_row(model, decls, phase_label):
    """
    Appends one CSV row with requested fields.
    Safe to call for both adaptive and residual runs.
    """
    # header once
    need_header = not os.path.exists(LOG_PATH)
    with open(LOG_PATH, "a", newline="") as f:
        w = csv.writer(f)
        if need_header:
            w.writerow([
                "ConfigNo","Phase","ResidualRisk","Penalty",
                "ImpersResidual","ReplayResidual","SessionResidual",
                "AssetValue","DisabledOperations","RemovedCRUD"
            ])
        # fields
        CONFIG_COUNTER["n"] += 1
        cfg = CONFIG_COUNTER["n"]
        residual = _get(model, decls, "ResRisk")
        penalty  = _get(model, decls, "AuthorizationPenalty")  # may be N/A in adaptive
        impers   = _get(model, decls, "PRiskPImpersAttack")
        replay   = _get(model, decls, "PRiskReplayAttack")
        session  = _get(model, decls, "PRiskSessionAttack")
        assetv   = _get(model, decls, "AssetValue")
        disabled_ops = ",".join(_disabled_operations(model, decls))
        removed_crud = _removed_crud_by_asset(model, decls)
        w.writerow([
            cfg, phase_label,
            residual, penalty, impers, replay, session,
            assetv, disabled_ops, removed_crud
        ])
    # also echo where we saved
    print(f"[LOG] Saved row #{CONFIG_COUNTER['n']} to {LOG_PATH} for phase '{phase_label}'.")
# --------------------------------------

# ---------------------------------
# 1) Adaptive model
# ---------------------------------
solver = z3.Solver()
ast = z3.parse_smt2_file("/Users/kabashi/Desktop/The model copy/adapt_model_S1.smt2")
solver.add(ast)

model_values = {}
selected_auth = {}

if solver.check() == sat:
    status = "Satisfiable"
    print("Adaptive Model: Satisfiable\n")
    M = solver.model()
    decls = {d.name(): d.range() for d in M.decls()}  # name -> sort

    # Read primary metrics
    for k in primary_keys:
        srt = decls.get(k, RealSort())
        model_values[k] = model_value(M, k, srt)

    # Selected auth methods (enabled)
    for name in auth_methods:
        srt = decls.get(name, RealSort())
        val = model_value(M, name, srt)
        enabled = False
        if isinstance(val, bool):
            enabled = val
        elif isinstance(val, (int, float)) and val is not None and val > 0:
            enabled = True
        if enabled:
            selected_auth[name] = val

    print("Selected Authentication Methods:")
    if selected_auth:
        for method, val in selected_auth.items():
            print(f"  - {method}: {fmt(val)}")
    else:
        print("  (none)")

    print("\nMetrics Summary:")
    print(f"Security     = {fmt(model_values.get('Security'))} "
          f"(Conf: {fmt(model_values.get('Confidentiality'))} × {fmt(model_values.get('ConfPriority'))}, "
          f"Auth: {fmt(model_values.get('Authenticity'))} × {fmt(model_values.get('AuthentPriority'))}, "
          f"Integ: {fmt(model_values.get('Integrity'))} × {fmt(model_values.get('IntegPriority'))})")

    print(f"Usability    = {fmt(model_values.get('Usability'))} "
          f"(Effectiveness: {fmt(model_values.get('Effectiveness'))} × {fmt(model_values.get('EffectPriority'))}, "
          f"Efficiency: {fmt(model_values.get('Efficiency'))} × {fmt(model_values.get('EfficPriority'))})")

    print(f"Performance  = {fmt(model_values.get('Performance'))} "
          f"(AvgPerformance: {fmt(model_values.get('AvgPerformance'))} × Priority: {fmt(model_values.get('PerformancePriority'))})")

    print(f"ResidualRisk = {fmt(model_values.get('ResRisk'))}")
    print(f"PImpersAttack = {fmt(model_values.get('PImpersAttack'))}")
    print(f"PSessionAttack = {fmt(model_values.get('PSessionAttack'))}")
    print(f"PReplayAttack = {fmt(model_values.get('PReplayAttack'))}")
    print(f"TotalRisk    = {fmt(model_values.get('TotalRisk'))}")
    print(f"Utility      = {fmt(model_values.get('Utility'))}")

    print(f"PRiskPImpersAttack = {fmt(model_values.get('PRiskPImpersAttack'))}")
    print(f"PRiskReplayAttack  = {fmt(model_values.get('PRiskReplayAttack'))}")
    print(f"PRiskSessionAttack = {fmt(model_values.get('PRiskSessionAttack'))}")
    print(f"Asset Value  = {fmt(model_values.get('AssetValue'))}")
    print(f"TwoFactor    = {fmt(model_values.get('TwoFactor'))}")

    print_operations_block(model_values, title="Operations (adaptive run)")
    print_hierarchical_authorization(M, decls, title="Authorization (adaptive run)")
    # Log the adaptive configuration as Config 1
    log_config_row(M, decls, phase_label="Adaptive")


else:
    status = "NonSatisfiable"
    print("Adaptive Model: Unsatisfiable.\n")


# ---------------------------------
# 2) Residual / authorization model – runs & sweep
# ---------------------------------


def run_residual_with_bound(target_rr, rr_band=0.015, timeout_ms=30000, max_iters=200, min_step=0.003):
    """
    Solver()-only maximize AssetValue:
      - Enforce ResRisk in (target_rr - rr_band, target_rr)
      - Monotonically tighten: AssetValue >= best + step until UNSAT or limits.
      - No penalty minimization.
    """
    # --- Base solver with fixed constraints ---
    base = z3.Solver()
    base.set(timeout=timeout_ms)

    ast_res = z3.parse_smt2_file("/Users/kabashi/Desktop/The model copy/residual_model_S1.smt2")
    base.add(ast_res)

    # Carry over auth choices + baseline Utility from adaptive run
    if status == "Satisfiable":
        chosen = set(selected_auth.keys())
        for name in auth_methods:
            srt = decls.get(name, RealSort()) if 'decls' in globals() else RealSort()
            c = as_constraint(name, srt, truthy=(name in chosen))
            if c is not None:
                base.add(c)
        base_util = model_values.get('Utility', None)
        if isinstance(base_util, (int, float)):
            base.add(Real('Utility') >= base_util)

    # Residual risk narrow band
    ResRisk    = Real('ResRisk')
    AssetValue = Real('AssetValue')

    base.add(ResRisk < RealVal(float(target_rr)))
    base.add(ResRisk > RealVal(float(target_rr)) - RealVal(rr_band))

    # -----------------------------
    # Phase A: push AssetValue up
    # -----------------------------
    s = z3.Solver()
    s.set(timeout=timeout_ms)
    s.add(base.assertions())

    r = s.check()
    if r != z3.sat:
        msg = "UNSAT" if r == z3.unsat else f"UNKNOWN ({s.reason_unknown()})"
        print(f"\nResidual/Authorization Model: {msg} at ResRisk ≤ {float(target_rr):.2f}\n")
        return False

    M = s.model()
    try:
        best_asset = float(str(M.eval(AssetValue)))
    except Exception:
        v = model_value(M, "AssetValue", RealSort())
        best_asset = float(v) if isinstance(v, (int,float)) else 0.0
    best_model = M

    # Monotone tightening loop: AssetValue >= best + step
    step = 0.02   # coarse start
    iters = 0
    while iters < max_iters:
        iters += 1
        target_asset = best_asset + step
        s.push()
        s.add(AssetValue >= RealVal(target_asset))
        r = s.check()
        if r == z3.sat:
            M2 = s.model()
            try:
                new_asset = float(str(M2.eval(AssetValue)))
            except Exception:
                v = model_value(M2, "AssetValue", RealSort())
                new_asset = float(v) if isinstance(v, (int,float)) else best_asset
            best_asset = new_asset
            best_model = M2
            s.pop()
            # adapt step: faster far from 1, finer near 1
            if best_asset < 0.6:
                step = max(step, 0.05)
            elif best_asset < 0.85:
                step = 0.01
            else:
                step = max(min_step, 0.002)
        elif r == z3.unsat:
            s.pop()
            if step <= min_step:
                break
            step /= 2.0
        else:  # unknown/timeout
            s.pop()
            if step <= min_step:
                break
            step /= 2.0

    if best_model is None:
        print(f"\nResidual/Authorization Model: No model in band at ResRisk ≤ {float(target_rr):.2f}\n")
        return False

    Final = best_model
    decls_res = {d.name(): d.range() for d in Final.decls()}

    # ---- print & log (unchanged) ----
    residual_values = {k: model_value(Final, k, decls_res.get(k, RealSort())) for k in
        ["Utility","ResRisk","AssetValue","Controlled","NonControlled","ViewLabResults",
         "AddEncounterNote","AddReferralNote","DiagnoseMedicalConditions","GenerateReports",
         "AuthorizationScore","Must","Nice","Optional","AuthorizationPenalty","AuthUtility",
         "PRiskSessionAttack","PRiskReplayAttack","PRiskPImpersAttack"]}

    residual_auth = {}
    for name in auth_methods:
        srt = decls_res.get(name, RealSort())
        val = model_value(Final, name, srt)
        enabled = (val is True) or (isinstance(val, (int,float)) and val is not None and val > 0)
        if enabled:
            residual_auth[name] = val

    print(f"\nResidual/Authorization Model: Satisfiable at ResRisk ≤ {float(target_rr):.2f}\n")
    print("Selected Authentication Methods (residual run):")
    if residual_auth:
        for method, val in residual_auth.items():
            print(f"  - {method}: {fmt(val)}")
    else:
        print("  (none)")

    print_hierarchical_authorization(Final, decls_res, title="Authorization (residual run)")
    print(f"\nUtility = {fmt(residual_values.get('Utility'))}")
    print_operations_block(residual_values, title="Operations (residual run)")
    print(f"Asset Value   = {fmt(residual_values.get('AssetValue'))}")
    print(f"Residual Risk = {fmt(residual_values.get('ResRisk'))}")
    print(f"Imper Residual Risk   = {fmt(residual_values.get('PRiskPImpersAttack'))}")
    print(f"Replay Residual Risk  = {fmt(residual_values.get('PRiskReplayAttack'))}")
    print(f"Session Residual Risk = {fmt(residual_values.get('PRiskSessionAttack'))}")
    print(f"Penalty       = {fmt(residual_values.get('AuthorizationPenalty'))}")
    print(f"AuthUtility   = {fmt(residual_values.get('AuthUtility'))}")

    log_config_row(Final, decls_res, phase_label=f"Residual_{float(target_rr):.3f}")
    return True


def sweep_residual(step=0.05, start=None):
    """
    Try progressively stricter residual-risk bounds:
      start (default: adaptive ResRisk) → start - step → ... until UNSAT.
    """
    if start is None:
        start = model_values.get('ResRisk', None)

    if start is None:
        print("No starting residual risk available from adaptive model.")
        return

    try:
        target = float(start)
    except Exception:
        print(f"Invalid starting residual risk: {start}")
        return

    idx = 1
    while target >= -1e-9:
        print(f"\n=== SWEEP #{idx}: Trying ResRisk ≤ {target:.2f} ===")
        ok = run_residual_with_bound(target)
        if not ok:
            print(f"Stopping sweep at bound {target:.2f} (UNSAT).")
            break
        idx += 1
        target -= step


sweep_residual(step=0.01)  # starts from the adaptive model's ResRisk