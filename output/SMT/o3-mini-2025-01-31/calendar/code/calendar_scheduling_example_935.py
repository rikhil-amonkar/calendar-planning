from z3 import Optimize, Int, Or, If, sat

# Helper functions to convert between "HH:MM" strings and minutes since midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")    # Work day starts at 9:00 (540 minutes).
work_end   = time_to_minutes("17:00")    # Work day ends at 17:00 (1020 minutes).

# Allowed days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3, Friday=4.
allowed_days = [0, 1, 2, 3, 4]

# Busy intervals for Terry.
terry_busy = {
    0: [  # Monday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:30"), time_to_minutes("14:00")),
        (time_to_minutes("15:00"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:30"),  time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:30"),  time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("9:30"),  time_to_minutes("10:00")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    4: [  # Friday
        (time_to_minutes("9:00"),  time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Busy intervals for Frances.
frances_busy = {
    0: [  # Monday
        (time_to_minutes("9:30"),  time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"),  time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:30"),  time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("14:30"), time_to_minutes("17:00"))
    ],
    4: [  # Friday
        (time_to_minutes("9:30"),  time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Create a Z3 Optimize solver.
opt = Optimize()

# Decision variables:
# meeting_day: 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday, 4 for Friday.
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: start time (in minutes since midnight) on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting time to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Frances would like to avoid more meetings on Tuesday.
opt.add_soft(meeting_day != 1, weight=1)

# Function to add busy constraints for a participant given their busy schedule dictionary.
def add_daily_busy(busy_schedule):
    for day, intervals in busy_schedule.items():
        for b_start, b_end in intervals:
            # If the meeting is on that day, then it must not overlap with the busy interval.
            opt.add(If(meeting_day == day,
                       Or(meeting_end <= b_start, meeting_start >= b_end),
                       True))

# Add busy constraints for Terry and Frances.
add_daily_busy(terry_busy)
add_daily_busy(frances_busy)

# Objective: schedule the meeting at the earliest availability.
# We'll minimize: overall_time = meeting_day * 1440 + meeting_start.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve and display the meeting time.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration
    
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(chosen_start))
    print("End:   ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")