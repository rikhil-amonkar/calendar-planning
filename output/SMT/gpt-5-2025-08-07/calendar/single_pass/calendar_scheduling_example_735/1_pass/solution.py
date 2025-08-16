# Solve the scheduling problem using Z3 to find the earliest feasible 30-minute meeting
from z3 import *

def time_to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

# Problem data
day_names = ["Monday", "Tuesday", "Wednesday"]
work_start = time_to_min("09:00")
work_end = time_to_min("17:00")
duration = 30  # minutes

# Blocked schedules per person per day index (0=Mon,1=Tue,2=Wed), times in minutes
blocked = {
    "Ronald": {
        0: [(time_to_min("10:30"), time_to_min("11:00")),
            (time_to_min("12:00"), time_to_min("12:30")),
            (time_to_min("15:30"), time_to_min("16:00"))],
        1: [(time_to_min("09:00"), time_to_min("09:30")),
            (time_to_min("12:00"), time_to_min("12:30")),
            (time_to_min("15:30"), time_to_min("16:30"))],
        2: [(time_to_min("09:30"), time_to_min("10:30")),
            (time_to_min("11:00"), time_to_min("12:00")),
            (time_to_min("12:30"), time_to_min("13:00")),
            (time_to_min("13:30"), time_to_min("14:00")),
            (time_to_min("16:30"), time_to_min("17:00"))],
    },
    "Amber": {
        0: [(time_to_min("09:00"), time_to_min("09:30")),
            (time_to_min("10:00"), time_to_min("10:30")),
            (time_to_min("11:30"), time_to_min("12:00")),
            (time_to_min("12:30"), time_to_min("14:00")),
            (time_to_min("14:30"), time_to_min("15:00")),
            (time_to_min("15:30"), time_to_min("17:00"))],
        1: [(time_to_min("09:00"), time_to_min("09:30")),
            (time_to_min("10:00"), time_to_min("11:30")),
            (time_to_min("12:00"), time_to_min("12:30")),
            (time_to_min("13:30"), time_to_min("15:30")),
            (time_to_min("16:30"), time_to_min("17:00"))],
        2: [(time_to_min("09:00"), time_to_min("09:30")),
            (time_to_min("10:00"), time_to_min("10:30")),
            (time_to_min("11:00"), time_to_min("13:30")),
            (time_to_min("15:00"), time_to_min("15:30"))],
    }
}

# Z3 variables
day = Int("day")       # 0=Mon, 1=Tue, 2=Wed
start = Int("start")   # minutes from 00:00 of that day
end = Int("end")

opt = Optimize()

# Basic constraints
opt.add(And(day >= 0, day <= 2))
opt.add(end == start + duration)
opt.add(And(work_start <= start, start <= work_end - duration))
# Optional: align to 30-minute boundaries
opt.add(start % 30 == 0)

# Non-overlap with blocked intervals for each participant
for person, sched in blocked.items():
    for d in range(3):
        for (bs, be) in sched.get(d, []):
            # If meeting is on day d, it must not overlap the blocked interval [bs, be)
            opt.add(Implies(day == d, Or(end <= bs, start >= be)))

# Objective: earliest possible across days and within day
start_of_week = day * 24 * 60 + start
opt.minimize(start_of_week)

if opt.check() != sat:
    raise RuntimeError("No feasible solution found, but one was expected.")

m = opt.model()
day_val = m[day].as_long()
start_val = m[start].as_long()
end_val = start_val + duration

def fmt(mins):
    h = mins // 60
    m_ = mins % 60
    return f"{h:02d}:{m_:02d}"

solution = [
    "SOLUTION:",
    f"Day: {day_names[day_val]}",
    f"Start Time: {fmt(start_val)}",
    f"End Time: {fmt(end_val)}",
]

print("\n".join(solution))