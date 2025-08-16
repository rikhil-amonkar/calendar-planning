from z3 import Optimize, Int, Or, Mod

# Helper functions
def t(h, m):
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Data
DAYS = ["Monday", "Tuesday", "Wednesday"]
WORK_START = t(9, 0)
WORK_END = t(17, 0)
DURATION = 30  # minutes

# Busy schedules in minutes since midnight
busy = {
    "Susan": {
        0: [(t(12, 30), t(13, 0)), (t(13, 30), t(14, 0))],
        1: [(t(11, 30), t(12, 0))],
        2: [(t(9, 30), t(10, 30)), (t(14, 0), t(14, 30)), (t(15, 30), t(16, 30))],
    },
    "Sandra": {
        0: [(t(9, 0), t(13, 0)), (t(14, 0), t(15, 0)), (t(16, 0), t(16, 30))],
        1: [(t(9, 0), t(9, 30)), (t(10, 30), t(12, 0)), (t(12, 30), t(13, 30)),
            (t(14, 0), t(14, 30)), (t(16, 0), t(17, 0))],
        2: [(t(9, 0), t(11, 30)), (t(12, 0), t(12, 30)), (t(13, 0), t(17, 0))],
    }
}

# Z3 variables
day = Int('day')        # 0=Monday, 1=Tuesday, 2=Wednesday
start = Int('start')    # minutes since midnight
end_time = start + DURATION

opt = Optimize()

# Day bounds
opt.add(day >= 0, day <= 2)

# Working hours and 30-minute grid
opt.add(start >= WORK_START)
opt.add(end_time <= WORK_END)
opt.add(Mod(start, 30) == 0)

# No overlap with busy intervals
for person, schedule in busy.items():
    for d, intervals in schedule.items():
        for (bs, be) in intervals:
            # If meeting is on day d, then it must not overlap with [bs, be)
            opt.add(Or(day != d, end_time <= bs, start >= be))

# Hard constraint: Sandra cannot meet on Monday after 16:00 (meeting must end by 16:00 if Monday)
opt.add(Or(day != 0, end_time <= t(16, 0)))

# Soft preference: Susan would rather not meet on Tuesday
opt.add_soft(day != 1, weight=1)

# Tie-breakers: choose earliest day, then earliest time
opt.minimize(day)
opt.minimize(start)

if opt.check() != sat:
    raise RuntimeError("No feasible schedule found.")

model = opt.model()
day_val = model[day].as_long()
start_val = model[start].as_long()
end_val = start_val + DURATION

print("SOLUTION:")
print(f"Day: {DAYS[day_val]}")
print(f"Start Time: {fmt(start_val)}")
print(f"End Time: {fmt(end_val)}")