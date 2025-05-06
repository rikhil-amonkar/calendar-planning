from z3 import Optimize, Int, Or, If, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # minutes
work_start = time_to_minutes("9:00")    # 540 minutes
work_end   = time_to_minutes("17:00")    # 1020 minutes

# Day encoding: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3, Friday = 4.
allowed_days = [0, 1, 2, 3, 4]

# Bryan's busy intervals (only specified on some days):
bryan_busy = {
    3: [  # Thursday
        (time_to_minutes("9:30"), time_to_minutes("10:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00"))
    ],
    4: [  # Friday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30"))
    ]
}

# Nicholas's busy intervals:
nicholas_busy = {
    0: [  # Monday
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("15:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"),  time_to_minutes("9:30")),
        (time_to_minutes("11:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("16:30"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"),  time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:30"))
    ],
    3: [  # Thursday
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    4: [  # Friday
        (time_to_minutes("9:00"),  time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables:
# meeting_day: integer representing the day, must be one of the allowed days.
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: start time in minutes after midnight on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add busy interval constraints for a given day.
def add_busy_constraints(day, busy_intervals):
    for b_start, b_end in busy_intervals:
        # If the meeting is scheduled on the specific day,
        # then it must not overlap with the busy interval.
        opt.add(If(meeting_day == day, Or(meeting_end <= b_start, meeting_start >= b_end), True))

# Add busy constraints for Bryan.
for day, intervals in bryan_busy.items():
    add_busy_constraints(day, intervals)

# Add busy constraints for Nicholas.
for day, intervals in nicholas_busy.items():
    add_busy_constraints(day, intervals)

# Add soft constraints (preferences):
# Bryan would like to avoid meetings on Tuesday (day == 1).
opt.add_soft(meeting_day != 1, weight=1)
# Nicholas would rather not meet on Monday (day == 0) or Thursday (day == 3).
opt.add_soft(meeting_day != 0, weight=1)
opt.add_soft(meeting_day != 3, weight=1)

# Objective: choose the earliest overall meeting time.
# We define an overall time as: overall_time = meeting_day * 1440 + meeting_start.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Check for a solution and print it.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")