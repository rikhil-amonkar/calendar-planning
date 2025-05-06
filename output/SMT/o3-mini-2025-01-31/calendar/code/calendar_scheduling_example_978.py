from z3 import Optimize, Int, Or, If, sat

# Helper functions to convert times.
def time_to_minutes(t):
    # Time t is in "HH:MM" format.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one hour
work_start = time_to_minutes("9:00")    # 540 minutes
work_end   = time_to_minutes("17:00")    # 1020 minutes

# Allowed days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3, Friday=4.
allowed_days = [0, 1, 2, 3, 4]

# Busy intervals for Brian on each day.
brian_busy = {
    0: [  # Monday
        (time_to_minutes("9:30"),  time_to_minutes("10:00")),
        (time_to_minutes("12:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"),  time_to_minutes("9:30"))
    ],
    2: [  # Wednesday
        (time_to_minutes("12:30"), time_to_minutes("14:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    4: [  # Friday
        (time_to_minutes("9:30"),  time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Busy intervals for Julia on each day.
julia_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"),  time_to_minutes("10:00")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"),  time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("9:00"),  time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("17:00"))
    ],
    4: [  # Friday
        (time_to_minutes("9:00"),  time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ]
}

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables:
# meeting_day: which day the meeting is held (0 to 4).
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: start time in minutes from midnight on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Brian would like to avoid more meetings on Monday.
# Add this as a soft constraint.
opt.add_soft(meeting_day != 0, weight=1)

# Helper function to add busy interval constraints for a given day.
def add_busy_constraints(day, busy_intervals):
    for (b_start, b_end) in busy_intervals:
        # When meeting is on this day, ensure no overlap with the busy interval.
        opt.add(If(meeting_day == day,
                   Or(meeting_end <= b_start, meeting_start >= b_end),
                   True))

# Add busy constraints for Brian.
for day, intervals in brian_busy.items():
    add_busy_constraints(day, intervals)
    
# Add busy constraints for Julia.
for day, intervals in julia_busy.items():
    add_busy_constraints(day, intervals)

# Objective: schedule at the earliest overall availability.
# Map overall time as: overall_time = meeting_day * 1440 + meeting_start.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve and print meeting time.
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