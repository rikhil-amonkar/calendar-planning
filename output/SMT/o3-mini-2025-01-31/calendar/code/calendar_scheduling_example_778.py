from z3 import Optimize, Int, Or, If, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration
meeting_duration = 30  # minutes
work_start = time_to_minutes("9:00")
work_end   = time_to_minutes("17:00")

# Day encoding: Monday = 0, Tuesday = 1, Wednesday = 2.
allowed_days = [0, 1, 2]

# Busy intervals for Susan on each day.
susan_busy = {
    0: [  # Monday
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("11:30"), time_to_minutes("12:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:30"), time_to_minutes("10:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ]
}

# Busy intervals for Sandra on each day.
sandra_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"),  time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"),  time_to_minutes("9:30")),
        (time_to_minutes("10:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"),  time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("17:00"))
    ]
}

# Additional participant preferences:
# Susan would rather not meet on Tuesday. We'll capture this by preferring earlier overall meeting times,
# as our objective will minimize (day*1440 + meeting_start) which naturally favors Monday (0) over Tuesday (1).
# Sandra cannot meet on Monday after 16:00. Hence, if meeting is on Monday, meeting_end must be <= 16:00.
sandra_monday_cutoff = time_to_minutes("16:00")

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables:
# meeting_day: must be one of the allowed days.
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: start time in minutes after midnight on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: meeting must be within the work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# If the meeting is on Monday, then Sandra's constraint forces meeting_end <= 16:00.
opt.add(If(meeting_day == 0, meeting_end <= sandra_monday_cutoff, True))

# Helper to add busy constraints for a participant on a given day.
def add_busy_constraints(day, busy_intervals):
    for b_start, b_end in busy_intervals:
        # If meeting is on the given day, then it must not overlap with the busy interval.
        opt.add(If(meeting_day == day, Or(meeting_end <= b_start, meeting_start >= b_end), True))

# Add busy constraints for Susan.
for day, intervals in susan_busy.items():
    add_busy_constraints(day, intervals)

# Add busy constraints for Sandra.
for day, intervals in sandra_busy.items():
    add_busy_constraints(day, intervals)

# Objective: We want the earliest available meeting time.
# We map the day and meeting start to an overall time in minutes:
# overall_time = meeting_day * 1440 + meeting_start.
# This ensures Monday is preferred over Tuesday, and Tuesday over Wednesday.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Check for and print a solution.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")