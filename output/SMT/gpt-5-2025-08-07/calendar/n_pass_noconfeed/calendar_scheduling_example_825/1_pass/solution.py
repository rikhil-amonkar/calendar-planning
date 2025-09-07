from z3 import *

# Days mapping
DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday"]

def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def rel_to_workday(t):
    # Workday starts at 09:00
    return to_min(t) - to_min("09:00")

def format_hhmm(minutes_from_0900):
    total = minutes_from_0900 + to_min("09:00")
    h = total // 60
    m = total % 60
    return f"{h:02d}:{m:02d}"

# Busy schedules per person per day (relative to 09:00)
# Day indices: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
laura_busy_str = {
    0: [("10:30", "11:00"), ("12:30", "13:00"), ("14:30", "15:30"), ("16:00", "17:00")],
    1: [("09:30", "10:00"), ("11:00", "11:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "17:00")],
    2: [("11:30", "12:00"), ("12:30", "13:00"), ("15:30", "16:30")],
    3: [("10:30", "11:00"), ("12:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")],
}
philip_busy_str = {
    0: [("09:00", "17:00")],
    1: [("09:00", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:00", "16:30")],
    2: [("09:00", "10:00"), ("11:00", "12:00"), ("12:30", "16:00"), ("16:30", "17:00")],
    3: [("09:00", "10:30"), ("11:00", "12:30"), ("13:00", "17:00")],
}

def convert_schedule(schedule_str):
    schedule = {}
    for d in range(4):
        intervals = []
        for s, e in schedule_str.get(d, []):
            intervals.append((rel_to_workday(s), rel_to_workday(e)))
        schedule[d] = intervals
    return schedule

laura_busy = convert_schedule(laura_busy_str)
philip_busy = convert_schedule(philip_busy_str)

# Z3 variables
day = Int("day")        # 0..3, but Wednesday (2) disallowed per constraint
start = Int("start")    # minutes from 09:00
duration = 60
end = start + duration

opt = Optimize()
opt.set(priority='lex')

# Day constraints: Monday..Thursday, but Philip cannot meet on Wednesday
opt.add(day >= 0, day <= 3, day != 2)

# Work hours constraints: between 09:00 and 17:00
opt.add(start >= 0)
opt.add(end <= rel_to_workday("17:00"))

# No-overlap constraints for each participant, conditional on chosen day
def no_overlap_for(schedule, d):
    intervals = schedule.get(d, [])
    if not intervals:
        return True
    return And([Or(end <= s, start >= e) for (s, e) in intervals])

# Apply conditional constraints per day
constraints = []
for d in range(4):
    constraints.append(If(day == d, no_overlap_for(laura_busy, d), True))
    constraints.append(If(day == d, no_overlap_for(philip_busy, d), True))
opt.add(constraints)

# Preference: choose earliest possible day and earliest possible start time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    d_val = m[day].as_long()
    s_val = m[start].as_long()
    e_val = s_val + duration
    day_name = DAYS[d_val]
    start_str = format_hhmm(s_val)
    end_str = format_hhmm(e_val)
    print(f"{day_name} {{{start_str}:{end_str}}}")
else:
    print("No solution found")