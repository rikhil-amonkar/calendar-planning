from z3 import Optimize, Int, Or, Implies, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # minutes
work_start = time_to_minutes("9:00")
work_end   = time_to_minutes("17:00")

# We can schedule on Monday (0) or Tuesday (1)
# Note: Based on Albert's schedule, Monday is completely busy.
# Allowed meeting days:
allowed_days = [0, 1]

# Busy intervals for each participant.
# Shirley's busy intervals:
shirley_busy = {
    0: [  # Monday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:30"), time_to_minutes("10:00"))
    ]
}
# Additional preference: On Tuesday, Shirley would rather not meet after 10:30;
# so if meeting is on Tuesday, the meeting must end by 10:30.
shirley_tuesday_deadline = time_to_minutes("10:30")

# Albert's busy intervals:
albert_busy = {
    0: [  # Monday: busy all day
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables:
# meeting_day: 0 for Monday, 1 for Tuesday.
meeting_day = Int("meeting_day")
# meeting_start: start time in minutes from midnight.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting_day to allowed days (Monday or Tuesday).
opt.add(Or([meeting_day == d for d in allowed_days]))

# Constrain meeting to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function: add busy constraints for a participant on a given day.
def add_busy_constraints(day, busy_intervals):
    for b_start, b_end in busy_intervals:
        # If meeting is on this day, it must not overlap with the busy interval.
        # (meeting_end <= busy_start) OR (meeting_start >= busy_end)
        opt.add(Implies(meeting_day == day, Or(meeting_end <= b_start, meeting_start >= b_end)))

# Add busy constraints for Shirley.
for day, intervals in shirley_busy.items():
    add_busy_constraints(day, intervals)

# Add busy constraints for Albert.
for day, intervals in albert_busy.items():
    add_busy_constraints(day, intervals)

# Add Shirley's Tuesday preference: if meeting is on Tuesday, the meeting must end by 10:30.
opt.add(Implies(meeting_day == 1, meeting_end <= shirley_tuesday_deadline))

# Objective: Schedule the meeting at the earliest availability.
# We minimize an overall time computed as: overall_time = meeting_day * 1440 + meeting_start.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Check for a solution.
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