from z3 import *

# Helper functions to convert time string (HH:MM) to minutes and vice versa.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one hour meeting
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")  # 1020 minutes

# Days are encoded as:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday

# Busy intervals (in minutes) for each participant on each day.

# Betty's busy intervals.
# Also note: Betty cannot meet on Wednesday or Thursday.
betty_busy = {
    0: [(time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))],
    1: [(time_to_minutes("9:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    2: [(time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))],
    3: [],  # Betty is free on Thursday but she has a constraint not to meet that day.
    4: [(time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))]
}

# Megan's busy intervals.
megan_busy = {
    0: [(time_to_minutes("9:00"), time_to_minutes("17:00"))],
    1: [(time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("12:00"), time_to_minutes("14:00")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))],
    2: [(time_to_minutes("9:30"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("17:00"))],
    3: [(time_to_minutes("9:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))],
    4: [(time_to_minutes("9:00"), time_to_minutes("17:00"))]
}

# Create Z3 solver.
s = Solver()

# Define variables:
# meeting_day: an integer in {0,1,2,3,4} representing the day of the week.
# meeting_start: the meeting start time in minutes from midnight.
meeting_day = Int("meeting_day")
s.add(Or(meeting_day == 0, meeting_day == 1, meeting_day == 2, meeting_day == 3, meeting_day == 4))

meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: Meeting must occur within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint 2: Apply Betty's day restrictions.
# Betty cannot meet on Wednesday (day 2) or Thursday (day 3).
s.add(meeting_day != 2, meeting_day != 3)

# Define a helper function to add constraints for a participant's busy intervals.
def add_busy_constraints(busy_dict):
    for day, intervals in busy_dict.items():
        for (busy_start, busy_end) in intervals:
            # If the meeting is scheduled on the same day, it must not overlap with the busy interval.
            s.add(Implies(meeting_day == day, Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Add constraints for Betty and Megan.
add_busy_constraints(betty_busy)
add_busy_constraints(megan_busy)

# Check for a valid meeting time.
if s.check() == sat:
    model = s.model()
    day_val = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[day_val])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")