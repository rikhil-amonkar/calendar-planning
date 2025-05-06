from z3 import Optimize, Int, Or, If, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # t is in "HH:MM" format.
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

# Allowed days: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
allowed_days = [0, 1, 2, 3]

# Busy intervals for Natalie.
natalie_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"),  time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"),  time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("12:30"), time_to_minutes("14:00")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    3: [  # Thursday
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Busy intervals for William.
william_busy = {
    0: [  # Monday
        (time_to_minutes("9:30"),  time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"),  time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("16:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"),  time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("9:00"),  time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("15:00"), time_to_minutes("17:00"))
    ]
}

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables: meeting_day and meeting_start time in minutes.
meeting_day = Int("meeting_day")
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Meeting must be scheduled on one of the allowed days.
opt.add(Or([meeting_day == d for d in allowed_days]))

# Meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add busy constraints for a given day.
def add_busy_constraints(day, busy_intervals):
    for b_start, b_end in busy_intervals:
        # On day 'day', meeting must not overlap the busy interval.
        opt.add(If(meeting_day == day, Or(meeting_end <= b_start, meeting_start >= b_end), True))

# Add busy constraints for Natalie.
for day, intervals in natalie_busy.items():
    add_busy_constraints(day, intervals)

# Add busy constraints for William.
for day, intervals in william_busy.items():
    add_busy_constraints(day, intervals)

# Objective: choose the earliest possible meeting time.
# Map the time to an overall number: overall_time = meeting_day * 1440 + meeting_start.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve and print a valid meeting time.
if opt.check() == sat:
    model = opt.model()
    day_val = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    
    print("A possible meeting time:")
    print("Day:   ", day_names[day_val])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")