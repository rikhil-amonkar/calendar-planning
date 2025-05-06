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

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# We'll later constrain meeting_day based on the participants' availability.

# Tyler's busy intervals:
# - Tuesday: 9:00 to 9:30 and 14:30 to 15:00.
# - Wednesday: 10:30 to 11:00, 12:30 to 13:00, 13:30 to 14:00, 16:30 to 17:00.
tyler_busy = {
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    # Monday: Tyler is free.
}

# Tyler's preference: avoid more meetings on Monday before 16:00.
preferred_monday_start = time_to_minutes("16:00")

# Ruth's busy intervals:
# - Monday: 9:00 to 10:00, 10:30 to 12:00, 12:30 to 14:30, 15:00 to 16:00, 16:30 to 17:00.
# - Tuesday: Busy all day (9:00 to 17:00).
# - Wednesday: Busy all day (9:00 to 17:00).
ruth_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"),  time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ]
}

# Create a Z3 solver instance.
s = Solver()

# Define an integer variable for the meeting day (0: Monday, 1: Tuesday, 2: Wednesday).
meeting_day = Int("meeting_day")
s.add(Or(meeting_day == 0, meeting_day == 1, meeting_day == 2))

# Define the meeting start time (in minutes).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: Meeting must be scheduled within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# If meeting is on Monday, enforce Tyler's preference to start no earlier than 16:00.
s.add(Implies(meeting_day == 0, meeting_start >= preferred_monday_start))

# Add constraints for Tyler's busy intervals.
for day, intervals in tyler_busy.items():
    for (busy_start, busy_end) in intervals:
        s.add(Implies(meeting_day == day,
                      Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Add constraints for Ruth's busy intervals.
for day, intervals in ruth_busy.items():
    for (busy_start, busy_end) in intervals:
        s.add(Implies(meeting_day == day,
                      Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Check for a valid meeting time.
if s.check() == sat:
    model = s.model()
    day_val = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[day_val]
    print("A possible meeting time:")
    print(f"Day:   {day_str}")
    print(f"Start: {minutes_to_time(start_val)}")
    print(f"End:   {minutes_to_time(end_val)}")
else:
    print("No valid meeting time could be found.")