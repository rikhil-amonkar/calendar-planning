from z3 import *

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration: half-hour meeting between 9:00 and 17:00.
meeting_duration = 30
work_start = time_to_minutes("9:00")    # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# Days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday.
# Define the busy intervals for Ruth on each day.
# Julie is free all week.
ruth_busy = {
    0: [  # Monday: busy 9:00 to 17:00
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday: busy 9:00 to 17:00
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday: busy 9:00 to 17:00
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday: busy intervals are 9:00-11:00, 11:30-14:30, and 15:00-17:00.
        (time_to_minutes("9:00"),  time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("17:00"))
    ]
}

# Julie's preference: Avoid meetings on Thursday before 11:30.
julie_thursday_pref = time_to_minutes("11:30")

# Create a Z3 solver instance.
s = Solver()

# Define an integer variable for the meeting day.
meeting_day = Int("meeting_day")
s.add(Or(meeting_day == 0, meeting_day == 1, meeting_day == 2, meeting_day == 3))

# Define the meeting start time (in minutes) as an integer variable.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: The meeting must occur within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Julie has no busy intervals, so no constraints for her schedule except her preference:
# If the meeting is on Thursday (day 3), then she prefers it not to start before 11:30.
s.add(Implies(meeting_day == 3, meeting_start >= julie_thursday_pref))

# Add constraints so that the meeting does not overlap Ruth's busy intervals.
for day, intervals in ruth_busy.items():
    for (busy_start, busy_end) in intervals:
        s.add(Implies(meeting_day == day,
                      Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Check for a valid meeting time that satisfies all constraints.
if s.check() == sat:
    model = s.model()
    day_val = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}[day_val]
    print("A possible meeting time:")
    print("Day:   ", day_str)
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")