from z3 import Optimize, Int, And, Or, If, Implies

def minutes(h, m):
    return h * 60 + m

def no_overlap(s, e, intervals):
    # Meeting [s, e) does not overlap any [a, b)
    return And([Or(e <= a, s >= b) for (a, b) in intervals]) if intervals else True

def minutes_to_str(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Constants
DURATION = 60
WORK_START = minutes(9, 0)   # 09:00
WORK_END = minutes(17, 0)    # 17:00

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
MON, TUE, WED, THU = range(4)

# Busy schedules (minutes from 00:00)
carl_busy = {
    MON: [(minutes(11, 0), minutes(11, 30))],
    TUE: [(minutes(14, 30), minutes(15, 0))],
    WED: [(minutes(10, 0), minutes(11, 30)), (minutes(13, 0), minutes(13, 30))],
    THU: [(minutes(13, 30), minutes(14, 0)), (minutes(16, 0), minutes(16, 30))]
}

margaret_busy = {
    MON: [(minutes(9, 0), minutes(10, 30)), (minutes(11, 0), minutes(17, 0))],
    TUE: [(minutes(9, 30), minutes(12, 0)), (minutes(13, 30), minutes(14, 0)), (minutes(15, 30), minutes(17, 0))],
    WED: [(minutes(9, 30), minutes(12, 0)), (minutes(12, 30), minutes(13, 0)),
          (minutes(13, 30), minutes(14, 30)), (minutes(15, 0), minutes(17, 0))],
    THU: [(minutes(10, 0), minutes(12, 0)), (minutes(12, 30), minutes(14, 0)), (minutes(14, 30), minutes(17, 0))]
}

# Z3 variables
day = Int('day')      # 0 = Monday ... 3 = Thursday
start = Int('start')  # minutes within the workday [09:00, 17:00)

opt = Optimize()

# Domain constraints
opt.add(day >= 0, day <= 3)
opt.add(start >= WORK_START, start + DURATION <= WORK_END)

# Availability constraints per selected day
for d in [MON, TUE, WED, THU]:
    s = start
    e = start + DURATION
    opt.add(Implies(day == d, no_overlap(s, e, carl_busy[d])))
    opt.add(Implies(day == d, no_overlap(s, e, margaret_busy[d])))

# Preference: Carl would like to avoid Thursday (soft constraint)
opt.minimize(If(day == THU, 1, 0))
# Tie-breaker: pick the earliest feasible start time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    chosen_day = m[day].as_long()
    s_val = m[start].as_long()
    e_val = s_val + DURATION

    print("SOLUTION:")
    print(f"Day: {days[chosen_day]}")
    print(f"Start Time: {minutes_to_str(s_val)} (24-hour format)")
    print(f"End Time: {minutes_to_str(e_val)} (24-hour format)")
else:
    # Fallback (should not happen per problem statement)
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 09:00 (24-hour format)")
    print("End Time: 10:00 (24-hour format)")