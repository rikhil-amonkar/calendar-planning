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
meeting_duration = 30  # half-hour meeting
work_start = time_to_minutes("9:00")   # 9:00 AM
work_end   = time_to_minutes("17:00")   # 5:00 PM

# Allowed days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
allowed_days = [0, 1, 2, 3]

# James's busy intervals for each day.
james_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("16:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("9:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Cheryl's calendar is completely free.
# However, Cheryl prefers not to meet on Wednesday and Thursday.
# We'll capture these as soft constraints.

# Create the Z3 optimizer.
opt = Optimize()

# Decision variable for meeting day.
# Days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# Decision variable for meeting start time in minutes (from midnight) on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function: add busy interval constraints (for James, in this case).
def add_busy_constraints(busy_schedule):
    for d in allowed_days:
        intervals = busy_schedule.get(d, [])
        for b_start, b_end in intervals:
            # If the meeting is scheduled on day d, it must either finish 
            # before the busy interval starts, or start after it ends.
            opt.add(If(meeting_day == d,
                       Or(meeting_end <= b_start, meeting_start >= b_end),
                       True))

# Add James's busy schedule constraints.
add_busy_constraints(james_busy)

# Cheryl's soft preferences:
# She would rather not meet on Wednesday (day 2) and Thursday (day 3).
opt.add_soft(meeting_day != 2, weight=1, id="avoid_wednesday")
opt.add_soft(meeting_day != 3, weight=1, id="avoid_thursday")

# Optionally, to schedule at the earliest availability, minimize overall time.
# This metric prioritizes earlier day and start time.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration
    
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(chosen_start))
    print("End:   ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")