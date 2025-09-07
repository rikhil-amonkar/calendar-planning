from z3 import *

# Meeting parameters
DURATION = 60  # minutes
WORK_START = 9 * 60   # 09:00 -> 540
WORK_END   = 17 * 60  # 17:00 -> 1020

# Days mapping
MON, TUE, WED = 0, 1, 2
day_names = {MON: "Monday", TUE: "Tuesday", WED: "Wednesday"}

# Z3 variables
day = Int('day')       # 0=Mon,1=Tue,2=Wed
start = Int('start')   # minutes since midnight for time-of-day
end = start + DURATION

opt = Optimize()

# Basic constraints
opt.add(And(day >= 0, day <= 2))
opt.add(And(start >= WORK_START, end <= WORK_END))
# 30-minute granularity
opt.add(start % 30 == 0)

# Busy intervals [start, end) in minutes since midnight
# Judith
judith_busy = {
    MON: [(12*60, 12*60 + 30)],     # 12:00-12:30
    TUE: [],
    WED: [(11*60 + 30, 12*60)]      # 11:30-12:00
}
# Timothy
timothy_busy = {
    MON: [
        (9*60 + 30, 10*60),         # 09:30-10:00
        (10*60 + 30, 11*60 + 30),   # 10:30-11:30
        (12*60 + 30, 14*60),        # 12:30-14:00
        (15*60 + 30, 17*60)         # 15:30-17:00
    ],
    TUE: [
        (9*60 + 30, 13*60),         # 09:30-13:00
        (13*60 + 30, 14*60),        # 13:30-14:00
        (14*60 + 30, 17*60)         # 14:30-17:00
    ],
    WED: [
        (9*60, 9*60 + 30),          # 09:00-09:30
        (10*60 + 30, 11*60),        # 10:30-11:00
        (13*60 + 30, 14*60 + 30),   # 13:30-14:30
        (15*60, 15*60 + 30),        # 15:00-15:30
        (16*60, 16*60 + 30)         # 16:00-16:30
    ]
}

def no_overlap_with(day_var, start_var, end_var, d, intervals):
    # For the chosen day d, meeting must not overlap with any interval
    for (bs, be) in intervals:
        opt.add(Implies(day_var == d, Or(end_var <= bs, start_var >= be)))

# Apply no-overlap constraints for each participant and each day
for d in [MON, TUE, WED]:
    no_overlap_with(day, start, end, d, judith_busy.get(d, []))
    no_overlap_with(day, start, end, d, timothy_busy.get(d, []))

# Preferences (soft constraints):
# - Judith would like to avoid more meetings on Monday.
opt.add_soft(day != MON, weight="10")
# - Judith would like to avoid Wednesday before 12:00.
opt.add_soft(Or(day != WED, start >= 12*60), weight="5")

# Secondary optimization: prefer earlier start times
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    chosen_day = m[day].as_long()
    s = m[start].as_long()
    e = s + DURATION

    def to_hhmm(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"

    day_str = day_names[chosen_day]
    start_str = to_hhmm(s)
    end_str = to_hhmm(e)

    print(day_str)
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No feasible solution found.")