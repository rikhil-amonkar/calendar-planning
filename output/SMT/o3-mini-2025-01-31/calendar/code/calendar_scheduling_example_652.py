from z3 import Solver, Int, Or, Implies

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")    # 540 minutes.
work_end   = time_to_minutes("17:00")   # 1020 minutes.

# Days Representation:
# 0 => Monday, 1 => Tuesday.
# Allowed days: Monday or Tuesday.
# Note: Lawrence is busy all day on Monday, so the meeting will end up on Tuesday.
day_options = [0, 1]

# Busy intervals for Monday and Tuesday for each participant.
# Times are represented in minutes from midnight.

# Jesse's busy intervals.
jesse_busy = {
    0: [  # Monday
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00"))
    ]
}

# Lawrence's busy intervals.
lawrence_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:30"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ]
}

# Additional constraint: Lawrence cannot meet on Tuesday after 16:30.
# This means if the meeting is on Tuesday, it must finish by 16:30.
lawrence_tuesday_latest_end = time_to_minutes("16:30")  # 990 minutes.

# Create a Z3 solver.
solver = Solver()

# Define decision variables.
meeting_day = Int("meeting_day")  # 0 for Monday, 1 for Tuesday.
solver.add(Or(meeting_day == day_options[0], meeting_day == day_options[1]))

# Define the meeting start time (in minutes).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: Meeting must occur within work hours.
solver.add(meeting_start >= work_start, meeting_end <= work_end)

# Additional constraint: If meeting is on Tuesday, Lawrence's meeting must finish by 16:30.
solver.add(Implies(meeting_day == 1, meeting_end <= lawrence_tuesday_latest_end))

# Helper function to add busy interval constraints.
def add_busy_constraints(busy_dict):
    for day, intervals in busy_dict.items():
        for start_busy, end_busy in intervals:
            # If the meeting is on 'day', then it must not overlap the busy interval.
            solver.add(Implies(meeting_day == day, Or(meeting_end <= start_busy, meeting_start >= end_busy)))

# Add constraints for Jesse and Lawrence.
add_busy_constraints(jesse_busy)
add_busy_constraints(lawrence_busy)

# Check for a valid meeting time.
if solver.check() == sat:
    model = solver.model()
    day_val = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration

    day_name = {0: "Monday", 1: "Tuesday"}
    print("A possible meeting time:")
    print("Day:   ", day_name[day_val])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")