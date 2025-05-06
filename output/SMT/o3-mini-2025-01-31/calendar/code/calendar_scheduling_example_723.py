from z3 import Optimize, Int, Or, Implies, sat

# Helper functions to convert between HH:MM strings and minutes since midnight.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration
meeting_duration = 30  # meeting duration in minutes
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# Allowed days: Monday = 0, Tuesday = 1, Wednesday = 2.
# Arthur cannot meet on Tuesday, so allowed days are Monday and Wednesday.
allowed_days = [0, 2]

# Busy intervals for Arthur and Michael organized by day.
# Monday = 0, Tuesday = 1, Wednesday = 2.
# Even though some busy intervals are provided for Tuesday, Arthur cannot meet on Tuesday,
# so we only need to consider Monday and Wednesday.

# Arthur's busy intervals
arthur_busy = {
    0: [  # Monday
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("15:00"), time_to_minutes("15:30"))
    ],
    2: [  # Wednesday
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
}

# Michael's busy intervals
michael_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("10:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30"))
    ]
}

# Create a Z3 Optimize solver instance.
opt = Optimize()

# Decision variables for meeting day and meeting start time (in minutes from midnight).
meeting_day = Int("meeting_day")
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting day to one of the allowed days (Monday or Wednesday).
opt.add(Or([meeting_day == d for d in allowed_days]))

# Ensure the meeting lies within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add busy constraints for a participant on a specific day.
def add_busy_constraints(day, busy_intervals):
    for b_start, b_end in busy_intervals:
        # If the meeting is on the given day, it must not overlap with the busy interval.
        opt.add(Implies(meeting_day == day, Or(meeting_end <= b_start, meeting_start >= b_end)))

# Add busy constraints for Arthur.
for day in allowed_days:
    if day in arthur_busy:
        add_busy_constraints(day, arthur_busy[day])

# Add busy constraints for Michael.
for day in allowed_days:
    if day in michael_busy:
        add_busy_constraints(day, michael_busy[day])

# Objective: Minimize overall start time, considering day and start time.
# We give each day 1440 minutes, so overall time = meeting_day * 1440 + meeting_start.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Check for a solution.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    day_names = {0: "Monday", 2: "Wednesday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")