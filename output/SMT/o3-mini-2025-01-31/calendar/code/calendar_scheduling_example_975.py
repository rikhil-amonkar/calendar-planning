from z3 import Optimize, Int, Or, Implies, sat

# Helper functions to convert time strings.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60
work_start = time_to_minutes("9:00")
work_end   = time_to_minutes("17:00")

# Define days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3, Friday=4.
days = [0, 1, 2, 3, 4]

# Busy intervals for Nicole (only specified for certain days):
# Tuesday: 16:00 to 16:30
nicole_busy = {
    1: [(time_to_minutes("16:00"), time_to_minutes("16:30"))],
    2: [(time_to_minutes("15:00"), time_to_minutes("15:30"))],  # Wednesday
    4: [(time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))]   # Friday
}

# Busy intervals for Daniel:
daniel_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("16:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("11:00"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("15:00"), time_to_minutes("15:30"))
    ],
    4: [  # Friday
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
}

# Create a Z3 Optimize solver.
opt = Optimize()

# Decision variable for meeting day (0 to 4) and meeting start time (in minutes).
meeting_day   = Int("meeting_day")
meeting_start = Int("meeting_start")
meeting_end   = meeting_start + meeting_duration

# meeting_day must be one of the allowed values.
opt.add(Or([meeting_day == d for d in days]))

# Constrain meeting time to work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# A helper function to add busy constraints for a participant on a given day.
def add_busy_constraints(day, busy_intervals):
    for b_start, b_end in busy_intervals:
        # If the meeting is on that day, then it must not overlap the busy interval.
        # That is, either meeting_end <= b_start OR meeting_start >= b_end.
        opt.add(Implies(meeting_day == day, Or(meeting_end <= b_start, meeting_start >= b_end)))

# Add constraints for Nicole.
for day, intervals in nicole_busy.items():
    add_busy_constraints(day, intervals)

# Add constraints for Daniel.
for day, intervals in daniel_busy.items():
    add_busy_constraints(day, intervals)

# To schedule the meeting at the earliest availability, we minimize the overall "absolute start time".
# We can convert the day and meeting_start into an overall time measure.
# Assume each day has 1440 minutes. Then overall_time = meeting_day * 1440 + meeting_start.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Check for a solution.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val   = start_val + meeting_duration
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")