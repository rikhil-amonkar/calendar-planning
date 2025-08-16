# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Or, Implies, If

# Constants
DURATION = 30  # minutes
WORK_START = 9 * 60          # 09:00 in minutes from 00:00
WORK_END = 17 * 60           # 17:00 in minutes from 00:00
WORK_WINDOW = WORK_END - WORK_START  # 480 minutes
DAYS = ["Monday", "Tuesday", "Wednesday"]

# Busy schedules as minutes from 09:00 of each day
# Each tuple is (start_minute_from_0900, end_minute_from_0900)
busy = {
    "Robert": {
        0: [(120, 150), (300, 330), (390, 420)],                               # Monday
        1: [(90, 120), (360, 390)],                                            # Tuesday
        2: [(60, 120), (150, 180), (210, 240), (270, 300), (360, 390), (420, 450)],  # Wednesday
    },
    "Ralph": {
        0: [(60, 270), (300, 330), (360, 480)],                                # Monday
        1: [(0, 30), (60, 90), (120, 150), (180, 240), (300, 390), (420, 480)],# Tuesday
        2: [(90, 120), (150, 180), (240, 330), (450, 480)],                    # Wednesday
    }
}

# Z3 variables
opt = Optimize()
opt.set(priority='lex')  # Lexicographic: earliest time first, then preferences
day = Int('day')         # 0=Mon, 1=Tue, 2=Wed
start = Int('start')     # minutes from 09:00 within selected day

# Domain constraints
opt.add(day >= 0, day <= 2)
opt.add(start >= 0, start + DURATION <= WORK_WINDOW)  # meeting within 09:00-17:00

# No-overlap constraints for both participants on the selected day
for d in range(3):
    # Gather all busy intervals for both participants on day d
    intervals = busy["Robert"][d] + busy["Ralph"][d]
    for (b_start, b_end) in intervals:
        # If this day is chosen, the meeting must not overlap this busy interval
        opt.add(Implies(day == d, Or(start + DURATION <= b_start, start >= b_end)))

# Objectives:
# 1) Earliest possible time in the week (primary)
global_start = day * WORK_WINDOW + start
opt.minimize(global_start)

# 2) Soft preference: avoid Monday (secondary)
avoid_monday = If(day == 0, 1, 0)  # 1 if Monday, else 0
opt.minimize(avoid_monday)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found, but a solution was expected.")

m = opt.model()
d_val = m[day].as_long()
s_val = m[start].as_long()

# Convert to 24-hour format
def to_hhmm(total_minutes_from_midnight):
    h = total_minutes_from_midnight // 60
    m_ = total_minutes_from_midnight % 60
    return f"{h:02d}:{m_:02d}"

start_abs = WORK_START + s_val              # minutes from midnight
end_abs = start_abs + DURATION

print("SOLUTION:")
print(f"Day: {DAYS[d_val]}")
print(f"Start Time: {to_hhmm(start_abs)}")
print(f"End Time: {to_hhmm(end_abs)}")