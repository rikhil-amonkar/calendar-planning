from z3 import Solver, Int, Or, Implies, sat

# Helper functions: convert "HH:MM" to minutes since midnight and vice versa.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # meeting lasts one hour.
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")  # 1020 minutes

# Days encoding:
# 0 -> Monday, 1 -> Tuesday.
allowed_days = [0, 1]

# Busy intervals for each participant.
# Each busy interval is a tuple (start, end) in minutes.
# Patricia's busy intervals.
patricia_busy = {
    0: [  # Monday
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:00")),
        (time_to_minutes("14:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Jesse's busy intervals.
jesse_busy = {
    0: [  # Monday: Jesse is busy all day.
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("17:00"))
    ]
}

# Create a Z3 solver.
solver = Solver()

# Decision variable for meeting day: 0 for Monday, 1 for Tuesday.
meeting_day = Int("meeting_day")
solver.add(Or(meeting_day == allowed_days[0], meeting_day == allowed_days[1]))

# Decision variable for meeting start time (in minutes).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: meeting must be within work hours.
solver.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add busy interval non-overlap constraints.
def add_busy_constraints(busy_intervals, day):
    for busy_start, busy_end in busy_intervals:
        # If meeting is scheduled on 'day', then it should not overlap the busy interval.
        solver.add(Implies(meeting_day == day, Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Add constraints for Patricia.
for day in patricia_busy:
    add_busy_constraints(patricia_busy[day], day)
    
# Add constraints for Jesse.
for day in jesse_busy:
    add_busy_constraints(jesse_busy[day], day)

# Check for a valid meeting time.
if solver.check() == sat:
    model = solver.model()
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