from z3 import Optimize, Int, Or, If, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    # Expects time in "HH:MM" format.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration
meeting_duration = 60  # one hour
work_start = time_to_minutes("9:00")    # 540 minutes
work_end   = time_to_minutes("17:00")    # 1020 minutes

# Allowed days: Monday (0), Tuesday (1), Wednesday (2), Thursday (3).
allowed_days = [0, 1, 2, 3]

# Busy intervals for Megan on each day.
megan_busy = {
    0: [  # Monday
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"),  time_to_minutes("9:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:30"),  time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("14:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    3: [  # Thursday
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30"))
    ]
}

# Busy intervals for Daniel on each day.
daniel_busy = {
    0: [  # Monday
        (time_to_minutes("10:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("15:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"),  time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"),  time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("9:00"),  time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ]
}

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_day (encoded as 0,1,2,3)
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# Decision variable: meeting_start time in minutes after midnight on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting to be within the workday hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add non-overlap busy constraints for a participant on a given day.
def add_busy_constraints(day, busy_intervals):
    for b_start, b_end in busy_intervals:
        # If meeting is scheduled on this day, it must not overlap with the busy interval.
        opt.add(If(meeting_day == day, Or(meeting_end <= b_start, meeting_start >= b_end), True))

# Add constraints for Megan.
for day, intervals in megan_busy.items():
    add_busy_constraints(day, intervals)

# Add constraints for Daniel.
for day, intervals in daniel_busy.items():
    add_busy_constraints(day, intervals)

# Objective: The group would like to meet at their earliest availability.
# We map a day and time to an overall score: overall_time = meeting_day * 1440 + meeting_start,
# then minimize overall_time.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Check for a solution.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_time))
    print("End:   ", minutes_to_time(end_time))
else:
    print("No valid meeting time could be found.")