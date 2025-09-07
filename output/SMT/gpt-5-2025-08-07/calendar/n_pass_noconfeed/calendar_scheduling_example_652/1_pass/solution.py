from z3 import *

# Meeting parameters
MEETING_DURATION = 30  # minutes
WORK_START = 0         # minutes from 9:00 (i.e., 9:00)
WORK_END = 480         # minutes from 9:00 (i.e., 17:00)

# Days
MONDAY, TUESDAY = 0, 1

# Helper to convert HH:MM to minutes from 9:00
def to_minutes(h, m):
    return (h - 9) * 60 + m

# Busy schedules as intervals [start, end) in minutes from 9:00
jesse_busy = {
    MONDAY: [
        (to_minutes(13, 30), to_minutes(14, 0)),
        (to_minutes(14, 30), to_minutes(15, 0)),
    ],
    TUESDAY: [
        (to_minutes(9, 0), to_minutes(9, 30)),
        (to_minutes(13, 0), to_minutes(13, 30)),
        (to_minutes(14, 0), to_minutes(15, 0)),
    ]
}

lawrence_busy = {
    MONDAY: [
        (to_minutes(9, 0), to_minutes(17, 0)),  # Busy all day Monday
    ],
    TUESDAY: [
        (to_minutes(9, 30), to_minutes(10, 30)),
        (to_minutes(11, 30), to_minutes(12, 30)),
        (to_minutes(13, 0), to_minutes(13, 30)),
        (to_minutes(14, 30), to_minutes(15, 0)),
        (to_minutes(15, 30), to_minutes(16, 30)),
    ]
}

# Lawrence cannot meet on Tuesday after 16:30 => meeting must end by 16:30 on Tuesday
TUESDAY_END_LIMIT = to_minutes(16, 30)

# Z3 variables
day = Int('day')
start = Int('start')
end = Int('end')

opt = Optimize()

# Day constraint: Monday or Tuesday
opt.add(Or(day == MONDAY, day == TUESDAY))

# Meeting within work hours
opt.add(start >= WORK_START)
opt.add(end == start + MEETING_DURATION)
opt.add(end <= WORK_END)

# No overlap with Jesse's busy times
for d in [MONDAY, TUESDAY]:
    for (bs, be) in jesse_busy[d]:
        # Either the meeting ends before a busy interval starts or starts after it ends
        opt.add(Implies(day == d, Or(end <= bs, start >= be)))

# No overlap with Lawrence's busy times
for d in [MONDAY, TUESDAY]:
    for (bs, be) in lawrence_busy[d]:
        opt.add(Implies(day == d, Or(end <= bs, start >= be)))

# Lawrence cannot meet on Tuesday after 16:30 (meeting must end by 16:30)
opt.add(Implies(day == TUESDAY, end <= TUESDAY_END_LIMIT))

# Optional: find the earliest valid day/time
opt.minimize(day)    # Prefer Monday over Tuesday if possible (but Monday is fully busy for Lawrence)
opt.minimize(start)  # Earliest time within the chosen day

if opt.check() != sat:
    raise RuntimeError("No feasible meeting time found.")

m = opt.model()
chosen_day = m[day].as_long()
chosen_start = m[start].as_long()
chosen_end = m[end].as_long()

def minutes_to_hhmm(minutes_from_9):
    total_minutes = minutes_from_9
    hour = 9 + (total_minutes // 60)
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

day_name = "Monday" if chosen_day == MONDAY else "Tuesday"
start_str = minutes_to_hhmm(chosen_start)
end_str = minutes_to_hhmm(chosen_end)

# Output: day of the week and time range in {HH:MM:HH:MM}
print(day_name)
print(f"{{{start_str}:{end_str}}}")