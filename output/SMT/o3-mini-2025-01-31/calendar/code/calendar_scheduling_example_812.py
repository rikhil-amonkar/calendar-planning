from z3 import Optimize, Int, Or, Implies, sat

# Helper functions.
def time_to_minutes(t):
    # Converts "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight to "HH:MM" format.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")   # 540 minutes.
work_end   = time_to_minutes("17:00")  # 1020 minutes.

# Days encoding:
# 0 -> Monday, 1 -> Tuesday, 2 -> Wednesday, 3 -> Thursday.
possible_days = [0, 1, 2, 3]

# Busy schedules for Mary.
# If a day is not specified, Mary is free on that day.
mary_busy = {
    1: [  # Tuesday
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:30"), time_to_minutes("10:00")),
        (time_to_minutes("15:00"), time_to_minutes("15:30"))
    ],
    3: [  # Thursday
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30"))
    ]
}

# Busy schedules for Alexis.
alexis_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("16:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("10:00"), time_to_minutes("12:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Create an Optimize object to minimize for earliest availability.
opt = Optimize()

# Decision variables:
# meeting_day: 0 (Monday) to 3 (Thursday)
# meeting_start: the starting time (in minutes) of the meeting on that day.
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in possible_days]))
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: meeting must fit in work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function: add constraints that meeting does not overlap a busy interval.
def add_busy_constraints(busy_intervals, day_val):
    for busy_start, busy_end in busy_intervals:
        # For the meeting on given day, it should either finish before a busy interval starts 
        # or start after that busy interval ends.
        opt.add(Implies(meeting_day == day_val, Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Add constraints for Mary's busy intervals.
for day, intervals in mary_busy.items():
    add_busy_constraints(intervals, day)

# Add constraints for Alexis's busy intervals.
for day, intervals in alexis_busy.items():
    add_busy_constraints(intervals, day)

# Objective: The group would like the meeting at their earliest availability.
# We want to minimize based on day and meeting_start.
# We'll combine both into one objective: meeting_day*10000 + meeting_start
# This ensures that a lower day (e.g. Monday) is prioritized and within a day, earlier start times are preferred.
opt.minimize(meeting_day * 10000 + meeting_start)

# Check and print solution.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")