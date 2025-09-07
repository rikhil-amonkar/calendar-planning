# Requires: z3-solver
from z3 import Int, Optimize, Or, sat

def to_minutes(hh_mm):
    hh, mm = map(int, hh_mm.split(':'))
    return hh * 60 + mm

def fmt_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Problem data
day = "Monday"
work_start = to_minutes("09:00")
work_end   = to_minutes("17:00")
duration = 60  # minutes

# Busy schedules as half-open intervals [start, end)
# Ryan: 9:00-9:30, 12:30-13:00
ryan_busy = [
    (to_minutes("09:00"), to_minutes("09:30")),
    (to_minutes("12:30"), to_minutes("13:00")),
]

# Ruth: no meetings
ruth_busy = []

# Denise: 9:30-10:30, 12:00-13:00, 14:30-16:30
denise_busy = [
    (to_minutes("09:30"), to_minutes("10:30")),
    (to_minutes("12:00"), to_minutes("13:00")),
    (to_minutes("14:30"), to_minutes("16:30")),
]

# Preference: Denise does not want to meet after 12:30 -> meeting must end by 12:30
denise_end_by = to_minutes("12:30")

# Z3 variables
S = Int("start")  # start time in minutes from 00:00
E = Int("end")    # end time in minutes from 00:00

opt = Optimize()

# Basic constraints
opt.add(E == S + duration)
opt.add(S >= work_start, E <= work_end)

# Preference constraint (hard)
opt.add(E <= denise_end_by)

def no_overlap_with_busy(start, end, busy_intervals):
    # For each busy interval [b_s, b_e), enforce (end <= b_s) or (start >= b_e)
    return [Or(end <= b_s, start >= b_e) for (b_s, b_e) in busy_intervals]

# No overlap constraints for all participants
opt.add(no_overlap_with_busy(S, E, ryan_busy))
opt.add(no_overlap_with_busy(S, E, ruth_busy))
opt.add(no_overlap_with_busy(S, E, denise_busy))

# Optional: pick the earliest feasible meeting start
opt.minimize(S)

if opt.check() == sat:
    m = opt.model()
    start_min = m[S].as_long()
    end_min = m[E].as_long()
    print(f"{day} {{{fmt_time(start_min)}-{fmt_time(end_min)}}}")
else:
    print("No feasible meeting time found.")