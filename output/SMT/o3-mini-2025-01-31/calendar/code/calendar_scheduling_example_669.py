from z3 import Optimize, Int, Or, Implies, sat

# Helper functions to convert time strings.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# Define meeting days: Monday = 0, Tuesday = 1.
# Allowed day variable.
meeting_day = Int("meeting_day")
allowed_days = [0, 1]
day_constraint = Or(meeting_day == allowed_days[0], meeting_day == allowed_days[1])

# Busy intervals for participants:
# Jean is only busy on Tuesday.
jean_busy_tuesday = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Doris is busy on both Monday and Tuesday.
doris_busy_monday = [
    (time_to_minutes("9:00"),  time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]
doris_busy_tuesday = [
    (time_to_minutes("9:00"),  time_to_minutes("17:00"))
]

# Doris would rather not meet on Monday after 14:00, 
# so enforce that if meeting is on Monday then meeting must finish by 14:00.
doris_preference_monday_deadline = time_to_minutes("14:00")

# Create solver.
opt = Optimize()
opt.add(day_constraint)

# Meeting start decision variable (in minutes since midnight).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Add participant busy constraints using conditional (if meeting on a certain day then...)
# For Jean:
# On Tuesday, avoid Jean's busy intervals.
for busy_start, busy_end in jean_busy_tuesday:
    opt.add(Implies(meeting_day == 1, Or(meeting_end <= busy_start, meeting_start >= busy_end)))
    
# For Doris:
# On Monday, avoid Doris's busy intervals and respect her preference not to meet after 14:00.
for busy_start, busy_end in doris_busy_monday:
    opt.add(Implies(meeting_day == 0, Or(meeting_end <= busy_start, meeting_start >= busy_end)))
opt.add(Implies(meeting_day == 0, meeting_end <= doris_preference_monday_deadline))

# On Tuesday, Doris is busy all day.
for busy_start, busy_end in doris_busy_tuesday:
    opt.add(Implies(meeting_day == 1, Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Objective: choose the earliest possible meeting time.
opt.minimize(meeting_start)

if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    day_names = {0: "Monday", 1: "Tuesday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")