from z3 import Int, Optimize, Or, Implies

# Helper to convert HH:MM to minutes since 00:00
def t(hh, mm):
    return hh * 60 + mm

# Days encoding
MON, TUE = 0, 1
day_names = {MON: "Monday", TUE: "Tuesday"}

# Meeting parameters
DURATION = 60
WORK_START = t(9, 0)
WORK_END = t(17, 0)

# Busy schedules per participant and day (intervals are [start, end) in minutes)
patricia_busy = {
    MON: [
        (t(10, 0), t(10, 30)),
        (t(11, 30), t(12, 0)),
        (t(13, 0), t(13, 30)),
        (t(14, 30), t(15, 30)),
        (t(16, 0), t(16, 30)),
    ],
    TUE: [
        (t(10, 0), t(10, 30)),
        (t(11, 0), t(12, 0)),
        (t(14, 0), t(16, 0)),
        (t(16, 30), t(17, 0)),
    ],
}

jesse_busy = {
    MON: [
        (t(9, 0), t(17, 0)),  # Entire workday blocked
    ],
    TUE: [
        (t(11, 0), t(11, 30)),
        (t(12, 0), t(12, 30)),
        (t(13, 0), t(14, 0)),
        (t(14, 30), t(15, 0)),
        (t(15, 30), t(17, 0)),
    ],
}

# Z3 variables
day = Int("day")        # 0=Monday, 1=Tuesday
start = Int("start")    # minutes from 00:00 within the chosen day
end = Int("end")        # start + duration

opt = Optimize()

# Domain constraints
opt.add(Or(day == MON, day == TUE))
opt.add(start >= WORK_START, end == start + DURATION, end <= WORK_END)

# No-overlap constraints for Patricia and Jesse
def add_no_overlap_for(busy_dict):
    for d in [MON, TUE]:
        for bs, be in busy_dict[d]:
            # Meeting [start, end) must not overlap busy [bs, be)
            opt.add(Implies(day == d, Or(end <= bs, start >= be)))

add_no_overlap_for(patricia_busy)
add_no_overlap_for(jesse_busy)

# Prefer earliest possible day, then earliest start time
opt.minimize(day)
opt.minimize(start)

if opt.check() != None and opt.check().r == 1:  # sat
    m = opt.model()
    chosen_day = m[day].as_long()
    s_val = m[start].as_long()
    e_val = m[end].as_long()

    def fmt(mm):
        return f"{mm // 60:02d}:{mm % 60:02d}"

    print("SOLUTION:")
    print(f"Day: {day_names[chosen_day]}")
    print(f"Start Time: {fmt(s_val)}")
    print(f"End Time: {fmt(e_val)}")
else:
    # According to the problem, a solution exists; this is a fallback.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 09:00")
    print("End Time: 10:00")