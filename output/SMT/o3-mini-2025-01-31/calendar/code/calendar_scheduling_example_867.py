from z3 import Optimize, Int, If, Or, Implies, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")  # 1020 minutes

# Days encoding:
# 0 -> Monday, 1 -> Tuesday, 2 -> Wednesday, 3 -> Thursday.
# Betty cannot meet on Monday or Tuesday.
# Also, Betty cannot meet on Thursday before 15:00.
# Thus, for Betty the meeting day must be either Wednesday or Thursday 
# (with Thursday meetings subject to starting at or after 15:00).
allowed_days = [2, 3]

# Busy intervals for Betty and Scott.
# Each is a dictionary mapping day -> list of busy intervals (start, end) in minutes.
betty_busy = {
    # Monday (day 0) and Tuesday (day 1) are not allowed for Betty, so we don't need to list them.
    2: [  # Wednesday
        (time_to_minutes("9:30"), time_to_minutes("10:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30"))
    ],
    3: [  # Thursday
        (time_to_minutes("9:30"), time_to_minutes("10:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

scott_busy = {
    # Scott's busy intervals on days; note that he is busy on other days too 
    # but we only consider the days that might be chosen.
    2: [  # Wednesday
        (time_to_minutes("9:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    3: [  # Thursday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Create an Optimize solver to allow optimization of preferences.
opt = Optimize()

# Define decision variables.
meeting_day = Int("meeting_day")  # Allowed values: 2 (Wednesday) or 3 (Thursday)
opt.add(Or(meeting_day == allowed_days[0], meeting_day == allowed_days[1]))

# Define meeting start and end time in minutes.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: Meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Additional constraint from Betty's preference for Thursday:
# If meeting is on Thursday (day == 3), it must not start before 15:00.
opt.add(Implies(meeting_day == 3, meeting_start >= time_to_minutes("15:00")))

# Helper function: for a given list of busy intervals, ensure the meeting does not overlap.
def add_busy_constraints(busy_intervals):
    for start_busy, end_busy in busy_intervals:
        # The meeting must either finish before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= start_busy, meeting_start >= end_busy))

# Add busy constraints conditioned on the meeting day.
for day, intervals in betty_busy.items():
    for start_busy, end_busy in intervals:
        opt.add(Implies(meeting_day == day, Or(meeting_end <= start_busy, meeting_start >= end_busy)))
        
for day, intervals in scott_busy.items():
    for start_busy, end_busy in intervals:
        opt.add(Implies(meeting_day == day, Or(meeting_end <= start_busy, meeting_start >= end_busy)))

# Scott would like to avoid more meetings on Wednesday.
# We add a soft constraint to prefer Thursday (day == 3) by adding a penalty
# if meeting_day is Wednesday.
penalty = If(meeting_day == 2, 1, 0)
opt.minimize(penalty)

# As a secondary objective, we can aim for the earliest possible meeting start time.
opt.minimize(meeting_start)

# Check for a valid meeting time and print the result.
if opt.check() == sat:
    model = opt.model()
    day_val = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration

    day_names = {2: "Wednesday", 3: "Thursday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[day_val])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")