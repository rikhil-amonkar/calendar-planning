from z3 import Optimize, Int, Or, Implies

# Helper functions for converting time strings to/from minutes.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")   # 540 minutes.
work_end   = time_to_minutes("17:00")  # 1020 minutes.

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday.
# Robert would like to avoid additional meetings on Monday.
# So we restrict the meeting to be on Tuesday or Wednesday.
allowed_days = [1, 2]

# Busy intervals for each participant on each day are given in minutes.
# Only include days on which a meeting might be scheduled (Tuesday = 1, Wednesday = 2).

# Robert's busy intervals.
robert_busy = {
    1: [  # Tuesday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("15:00"), time_to_minutes("15:30"))
    ],
    2: [  # Wednesday
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
}

# Ralph's busy intervals.
ralph_busy = {
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Create an Optimize object.
opt = Optimize()

# Define decision variables.
meeting_day = Int("meeting_day")    # allowed values: 1 (Tuesday) or 2 (Wednesday)
opt.add(Or(meeting_day == allowed_days[0], meeting_day == allowed_days[1]))

meeting_start = Int("meeting_start")  # meeting start time in minutes (within work hours)
meeting_end = meeting_start + meeting_duration

# Constraint 1: Meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function: For a given participant busy intervals dictionary, 
# add the constraint that if the meeting is scheduled on that day, it must not overlap any busy interval.
def add_busy_constraints(busy_dict):
    for day, intervals in busy_dict.items():
        for (busy_start, busy_end) in intervals:
            opt.add(Implies(meeting_day == day,
                            Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Add busy constraints for both participants.
add_busy_constraints(robert_busy)
add_busy_constraints(ralph_busy)

# Objective: We want to schedule the meeting at the earliest availability.
# Here 'earliest' is defined lexicographically: first by day (Tuesday is preferred over Wednesday)
# and then by the meeting start time in that day.
# To capture this, we define an overall measure: total minutes = (day_value * 1440 + meeting_start).
total_minutes = meeting_day * 1440 + meeting_start
h_total = opt.minimize(total_minutes)

# Check for a solution.
if opt.check() == sat:
    model = opt.model()
    day_val = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration

    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A possible meeting time:")
    print("Day:   ", day_name[day_val])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")