from z3 import *

# Convert a time string HH:MM to minutes
def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

# Meeting configuration (one hour meeting)
meeting_duration = 60

# Workday boundaries in minutes (9:00 to 17:00)
work_start = time_to_minutes("9:00")   # 540 minutes
work_end = time_to_minutes("17:00")    # 1020 minutes

# Existing events from both participants in minutes.
# Each event is represented as a (start, end) tuple.
# James's events on Monday:
james_events = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# John's events on Monday:
john_events = [
    (time_to_minutes("9:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("16:30"))
]

# Combine all events since the meeting must avoid all.
all_events = james_events + john_events

# Create a Z3 solver instance
s = Solver()

# meeting_start is the starting time in minutes for the meeting.
meeting_start = Int("meeting_start")

# The meeting must start after the work day begins and end by or before work_end.
s.add(meeting_start >= work_start)
s.add(meeting_start + meeting_duration <= work_end)

# For each blocked event, the meeting must not overlap.
# To avoid overlapping with an event (event_start, event_end),
# we add the constraint: meeting_end <= event_start OR meeting_start >= event_end.
meeting_end = meeting_start + meeting_duration

for (e_start, e_end) in all_events:
    s.add(Or(meeting_end <= e_start, meeting_start >= e_end))

# Check if a solution exists
if s.check() == sat:
    model = s.model()
    start_minutes = model[meeting_start].as_long()
    end_minutes = start_minutes + meeting_duration

    # Convert minutes back to HH:MM format.
    def minutes_to_time(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"

    print("A possible meeting time:")
    print(f"Start: {minutes_to_time(start_minutes)}")
    print(f"End:   {minutes_to_time(end_minutes)}")
else:
    print("No valid meeting time could be found.")