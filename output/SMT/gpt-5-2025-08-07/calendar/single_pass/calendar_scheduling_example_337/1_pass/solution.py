from z3 import Int, Or, And, Optimize, sat

def minutes(h, m):
    return h * 60 + m

def minutes_to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Workday and meeting duration
WORK_START = minutes(9, 0)    # 540
WORK_END   = minutes(17, 0)   # 1020
DURATION   = 30               # minutes

# Busy schedules (start, end) in minutes from midnight
busy = {
    "John": [
        (minutes(11,30), minutes(12,0)),
        (minutes(14,0),  minutes(14,30)),
    ],
    "Megan": [
        (minutes(12,0),  minutes(12,30)),
        (minutes(14,0),  minutes(15,0)),
        (minutes(15,30), minutes(16,0)),
    ],
    "Brandon": [
        # No meetings
    ],
    "Kimberly": [
        (minutes(9,0),   minutes(9,30)),
        (minutes(10,0),  minutes(10,30)),
        (minutes(11,0),  minutes(14,30)),
        (minutes(15,0),  minutes(16,0)),
        (minutes(16,30), minutes(17,0)),
    ],
    "Sean": [
        (minutes(10,0),  minutes(11,0)),
        (minutes(11,30), minutes(14,0)),
        (minutes(15,0),  minutes(15,30)),
    ],
    "Lori": [
        (minutes(9,0),   minutes(9,30)),
        (minutes(10,30), minutes(12,0)),
        (minutes(13,0),  minutes(14,30)),
        (minutes(16,0),  minutes(16,30)),
    ],
}

# Z3 model
start = Int("start")
opt = Optimize()

# Meeting must be within work hours
opt.add(And(start >= WORK_START, start + DURATION <= WORK_END))

# Meeting cannot overlap any busy interval for any participant
for person, intervals in busy.items():
    for (s, e) in intervals:
        # No overlap: meeting entirely before interval OR entirely after interval
        opt.add(Or(start + DURATION <= s, start >= e))

# Optionally choose the earliest feasible time (deterministic nice pick)
opt.minimize(start)

if opt.check() != sat:
    raise RuntimeError("No feasible meeting time found, but a solution was expected.")

model = opt.model()
start_time = model[start].as_long()
end_time = start_time + DURATION

print("SOLUTION:")
print("Day: Monday")
print(f"Start Time: {minutes_to_hhmm(start_time)}")
print(f"End Time: {minutes_to_hhmm(end_time)}")