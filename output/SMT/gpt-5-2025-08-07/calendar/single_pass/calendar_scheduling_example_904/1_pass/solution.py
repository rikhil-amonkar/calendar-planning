from z3 import Optimize, Int, And, Or, Implies, Mod

# Helper functions
def t(hhmm):
    hh, mm = map(int, hhmm.split(":"))
    return hh * 60 + mm

def fmt(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Constants
DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
DAY_IDX = {d: i for i, d in enumerate(DAYS)}
WORK_START = t("09:00")
WORK_END = t("17:00")
DURATION = 30  # minutes

# Busy schedules (half-open intervals [start, end))
daniel_busy = {
    "Monday":    [(t("09:30"), t("10:30")), (t("12:00"), t("12:30")), (t("13:00"), t("14:00")),
                  (t("14:30"), t("15:00")), (t("15:30"), t("16:00"))],
    "Tuesday":   [(t("11:00"), t("12:00")), (t("13:00"), t("13:30")), (t("15:30"), t("16:00")),
                  (t("16:30"), t("17:00"))],
    "Wednesday": [(t("09:00"), t("10:00")), (t("14:00"), t("14:30"))],
    "Thursday":  [(t("10:30"), t("11:00")), (t("12:00"), t("13:00")), (t("14:30"), t("15:00")),
                  (t("15:30"), t("16:00"))],
    "Friday":    [(t("09:00"), t("09:30")), (t("11:30"), t("12:00")), (t("13:00"), t("13:30")),
                  (t("16:30"), t("17:00"))],
}

bradley_busy = {
    "Monday":    [(t("09:30"), t("11:00")), (t("11:30"), t("12:00")), (t("12:30"), t("13:00")),
                  (t("14:00"), t("15:00"))],
    "Tuesday":   [(t("10:30"), t("11:00")), (t("12:00"), t("13:00")), (t("13:30"), t("14:00")),
                  (t("15:30"), t("16:30"))],
    "Wednesday": [(t("09:00"), t("10:00")), (t("11:00"), t("13:00")), (t("13:30"), t("14:00")),
                  (t("14:30"), t("17:00"))],
    "Thursday":  [(t("09:00"), t("12:30")), (t("13:30"), t("14:00")), (t("14:30"), t("15:00")),
                  (t("15:30"), t("16:30"))],
    "Friday":    [(t("09:00"), t("09:30")), (t("10:00"), t("12:30")), (t("13:00"), t("13:30")),
                  (t("14:00"), t("14:30")), (t("15:30"), t("16:30"))],
}

# Z3 variables
day = Int("day")      # 0=Monday ... 4=Friday
start = Int("start")  # minutes since midnight
end = Int("end")

opt = Optimize()

# Basic bounds and duration
opt.add(day >= 0, day <= 4)
opt.add(start >= WORK_START, end == start + DURATION, end <= WORK_END)
# Start at 30-minute increments
opt.add(Mod(start, 30) == 0)

# Avoid overlapping any busy times for each participant on the chosen day
def no_overlap_constraints(schedule):
    cons = []
    for dname, idx in DAY_IDX.items():
        for (bs, be) in schedule[dname]:
            cons.append(Implies(day == idx, Or(end <= bs, start >= be)))
    return And(cons) if cons else True

opt.add(no_overlap_constraints(daniel_busy))
opt.add(no_overlap_constraints(bradley_busy))

# Preferences/constraints:
# Daniel would rather not meet on Wednesday, Thursday (treat as constraints here)
opt.add(day != DAY_IDX["Wednesday"])
opt.add(day != DAY_IDX["Thursday"])

# Bradley does not want Monday, Tuesday before 12:00, or Friday
opt.add(day != DAY_IDX["Monday"])
opt.add(day != DAY_IDX["Friday"])
opt.add(Implies(day == DAY_IDX["Tuesday"], start >= t("12:00")))

# Minimize lexicographically: earliest day, then earliest time
opt.minimize(day)
opt.minimize(start)

if opt.check() !=  sat:
    print("No solution found")
else:
    m = opt.model()
    sel_day = m[day].as_long()
    sel_start = m[start].as_long()
    sel_end = m[end].as_long()

    print("SOLUTION:")
    print(f"Day: {DAYS[sel_day]}")
    print(f"Start Time: {fmt(sel_start)} (24-hour format)")
    print(f"End Time: {fmt(sel_end)} (24-hour format)")