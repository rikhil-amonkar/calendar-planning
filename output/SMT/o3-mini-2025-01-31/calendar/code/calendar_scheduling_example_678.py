from z3 import Optimize, Int, Or, Implies, If, sat

# Helper functions to convert time string to minutes and vice versa.
def time_to_minutes(t):
    # "HH:MM" -> minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one hour meeting
work_start = time_to_minutes("9:00")   # 9:00 => 540 minutes
work_end   = time_to_minutes("17:00")   # 17:00 => 1020 minutes

# Days encoding:
# 0 -> Monday, 1 -> Tuesday.
allowed_days = [0, 1]

# Busy schedules.
# Russell's busy intervals.
# Monday: 10:30 to 11:00 -> (630, 690)
russell_monday = [(time_to_minutes("10:30"), time_to_minutes("11:00"))]
# Tuesday: 13:00 to 13:30 -> (780, 810)
russell_tuesday = [(time_to_minutes("13:00"), time_to_minutes("13:30"))]

# Alexander's busy intervals.
# Monday: 9:00-11:30, 12:00-14:30, 15:00-17:00.
alexander_monday = [
    (time_to_minutes("9:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("17:00"))
]
# Tuesday: 9:00-10:00, 13:00-14:00, 15:00-15:30, 16:00-16:30.
alexander_tuesday = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Create Optimize solver.
opt = Optimize()

# Decision variables:
meeting_day = Int("meeting_day")
opt.add(Or(meeting_day == allowed_days[0], meeting_day == allowed_days[1]))
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Add constraints for busy intervals.
def add_busy_constraints(busy_intervals, day_value):
    for (busy_start, busy_end) in busy_intervals:
        # If meeting is scheduled on day_value, then meeting must not overlap the busy interval.
        opt.add(Implies(meeting_day == day_value,
                        Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Add Russell's constraints.
add_busy_constraints(russell_monday, 0)
add_busy_constraints(russell_tuesday, 1)

# Additional Russell preference: "rather not meet on Tuesday before 13:30"
# Enforce that if meeting is on Tuesday, then meeting_start must be at or after 13:30.
opt.add(Implies(meeting_day == 1, meeting_start >= time_to_minutes("13:30")))

# Add Alexander's constraints.
add_busy_constraints(alexander_monday, 0)
add_busy_constraints(alexander_tuesday, 1)

# Optional: minimize the meeting start time to have the earliest possible meeting
# (if there is any tie, Monday is preferred because available times determine that automatically).
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