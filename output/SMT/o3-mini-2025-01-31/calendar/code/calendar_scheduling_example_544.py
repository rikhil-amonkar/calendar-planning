from z3 import *

# A helper function to convert HH:MM into minutes since midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

# Meeting configuration: half an hour (30 minutes).
meeting_duration = 30

# Work hours (9:00 to 17:00)
work_start = time_to_minutes("9:00")   # 540
work_end   = time_to_minutes("17:00")  # 1020

# Additional constraint: Albert cannot meet after 11:00.
latest_end = time_to_minutes("11:00")  # 660

# Deborah is free the entire day, so no blocked intervals for her.
# Albert's blocked intervals on Monday:
albert_events = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("15:00"), time_to_minutes("16:30"))
]

# Create a Z3 solver instance
s = Solver()

# Declare an integer variable representing the meeting start time in minutes.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: Meeting must be within work hours.
s.add(meeting_start >= work_start)
s.add(meeting_end <= work_end)

# Constraint 2: Meeting must finish by 11:00 since Albert cannot meet after 11:00.
s.add(meeting_end <= latest_end)

# Constraint 3: Ensure the meeting does not overlap any of Albert's blocked intervals.
# For each event, the meeting must finish before the event starts or start after the event ends.
for (event_start, event_end) in albert_events:
    s.add(Or(meeting_end <= event_start, meeting_start >= event_end))

# Check if a valid meeting time is found
if s.check() == sat:
    model = s.model()
    start_minutes = model[meeting_start].as_long()
    end_minutes = start_minutes + meeting_duration

    # Helper function to convert minutes back to HH:MM format.
    def minutes_to_time(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"

    print("A possible meeting time:")
    print(f"Start: {minutes_to_time(start_minutes)}")
    print(f"End:   {minutes_to_time(end_minutes)}")
else:
    print("No valid meeting time could be found.")