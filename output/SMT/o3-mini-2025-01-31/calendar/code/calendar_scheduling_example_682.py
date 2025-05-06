from z3 import Optimize, Int, Or, If, sat

# Helper functions to convert between "HH:MM" strings and minutes.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration
meeting_duration = 30  # half an hour
work_start = time_to_minutes("9:00")
work_end   = time_to_minutes("17:00")

# Allowed days: Monday = 0, Tuesday = 1.
allowed_days = [0, 1]

# Busy intervals for Amanda:
amanda_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"),  time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"),  time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Busy intervals for Nathan:
nathan_busy = {
    0: [  # Monday
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"),  time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
}

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables:
# meeting_day: 0 (Monday) or 1 (Tuesday)
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: start time in minutes from midnight on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting to occur within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Additional participant-specific day constraints:
# Nathan cannot meet on Monday.
opt.add(meeting_day != 0)

# Amanda does not want to meet on Tuesday after 11:00.
opt.add(If(meeting_day == 1, meeting_end <= time_to_minutes("11:00"), True))

# Helper function to add busy constraints:
def add_busy_constraints(day, busy_intervals):
    for b_start, b_end in busy_intervals:
        # If meeting is on the specified day, then
        # the meeting must not overlap with the busy interval.
        opt.add(If(meeting_day == day,
                   Or(meeting_end <= b_start, meeting_start >= b_end),
                   True))

# Add busy constraints for Amanda.
for day, intervals in amanda_busy.items():
    add_busy_constraints(day, intervals)

# Add busy constraints for Nathan.
for day, intervals in nathan_busy.items():
    add_busy_constraints(day, intervals)

# Objective: The group wants the earliest availability.
# We define an "overall" time measure as day*1440 + meeting_start.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve and print the final meeting time.
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