from z3 import *

# Helper functions to convert time formats.
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30 minutes meeting.
work_start = time_to_minutes("9:00")   # 540 minutes.
work_end   = time_to_minutes("17:00")  # 1020 minutes.

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Cheryl's busy intervals.
cheryl_busy = {
    0: [   # Monday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("11:30"), time_to_minutes("13:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    1: [   # Tuesday
        (time_to_minutes("15:00"), time_to_minutes("15:30"))
    ],
    2: []  # Although no busy intervals listed for Wednesday,
          # Cheryl cannot meet on Wednesday.
}

# Kyle's busy intervals.
kyle_busy = {
    0: [   # Monday
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    1: [   # Tuesday
        (time_to_minutes("9:30"), time_to_minutes("17:00"))
    ],
    2: [   # Wednesday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("17:00"))
    ]
}

# Create a Z3 solver instance.
s = Solver()

# Define a variable for the meeting day (0: Monday, 1: Tuesday, 2: Wednesday).
meeting_day = Int("meeting_day")
s.add(Or(meeting_day == 0, meeting_day == 1, meeting_day == 2))

# Constraint: Cheryl cannot meet on Wednesday.
s.add(meeting_day != 2)

# Define the meeting start time (in minutes).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: Meeting must be within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# For each busy interval of Cheryl, if the meeting is on that day then
# the meeting must not overlap the busy interval.
for day_val, intervals in cheryl_busy.items():
    for (busy_start, busy_end) in intervals:
        s.add(Implies(meeting_day == day_val, Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# For each busy interval of Kyle, if the meeting is on that day then
# the meeting must not overlap the busy interval.
for day_val, intervals in kyle_busy.items():
    for (busy_start, busy_end) in intervals:
        s.add(Implies(meeting_day == day_val, Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Check for a valid meeting time.
if s.check() == sat:
    model = s.model()
    chosen_day = model[meeting_day].as_long()
    start = model[meeting_start].as_long()
    end = start + meeting_duration
    
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[chosen_day]
    
    print("A possible meeting time:")
    print(f"Day:   {day_str}")
    print(f"Start: {minutes_to_time(start)}")
    print(f"End:   {minutes_to_time(end)}")
else:
    print("No valid meeting time could be found.")