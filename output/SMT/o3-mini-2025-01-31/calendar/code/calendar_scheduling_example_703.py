from z3 import Optimize, Int, Or, If, sat, Not

# Helper functions for time conversions.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one hour meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM
work_end   = time_to_minutes("17:00")   # 5:00 PM

# Allowed days: Monday = 0, Tuesday = 1, Wednesday = 2.
allowed_days = [0, 1, 2]

# Stephanie's busy intervals.
stephanie_busy = {
    0: [  # Monday
        (time_to_minutes("9:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("12:00"), time_to_minutes("13:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("13:00"), time_to_minutes("14:00"))
    ]
}

# Betty's busy intervals.
betty_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("10:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("17:00"))
    ]
}

# Create the Z3 optimizer.
opt = Optimize()

# Decision variable: meeting_day: Monday (0), Tuesday (1), Wednesday (2).
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# Decision variable: meeting_start time in minutes from midnight.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Betty's constraint: on Tuesday (day == 1) she cannot meet after 12:30.
tuesday_deadline = time_to_minutes("12:30")
opt.add(If(meeting_day == 1, meeting_end <= tuesday_deadline, True))

# Helper function to add constraints that meeting must not conflict with busy intervals.
def add_busy_constraints(schedule):
    for d in allowed_days:
        intervals = schedule.get(d, [])
        for b_start, b_end in intervals:
            # If meeting is on day d, then it must end before the busy interval starts OR start after it ends.
            opt.add(If(meeting_day == d,
                       Or(meeting_end <= b_start, meeting_start >= b_end),
                       True))

# Add busy constraints for both participants.
add_busy_constraints(stephanie_busy)
add_busy_constraints(betty_busy)

# Stephanie's preference: She would like to avoid more meetings on Monday.
# We add this as a soft constraint preferring meeting_day != 0.
opt.add_soft(meeting_day != 0, weight=1, id="stephanie_prefers_not_monday")

# Additionally, we choose the earliest possible meeting time as a secondary objective.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration

    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(chosen_start))
    print("End:   ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")