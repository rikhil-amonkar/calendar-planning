from z3 import *

# Helper function: Convert a time "HH:MM" into minutes since midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

# Meeting configuration
meeting_duration = 30  # 30 minutes meeting

# Workday boundaries: 9:00 to 17:00
work_start = time_to_minutes("9:00")    # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# Define each participant's busy intervals.
# Doris:
doris_events = [
    (time_to_minutes("9:00"), time_to_minutes("11:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Theresa:
theresa_events = [
    (time_to_minutes("10:00"), time_to_minutes("12:00"))
]

# Christian is free the entire day so no events.

# Terry:
terry_events = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Carolyn:
carolyn_events = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("17:00"))
]

# Kyle:
kyle_events = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("17:00"))
]

# Combine all busy intervals since the meeting must avoid every participant's blocks.
all_events = doris_events + theresa_events + terry_events + carolyn_events + kyle_events

# Create a Z3 solver instance.
s = Solver()

# Define an integer variable for the meeting start time in minutes.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: The meeting must start within work hours.
s.add(meeting_start >= work_start)
s.add(meeting_end <= work_end)

# Constraint 2: The meeting must not overlap any busy interval.
# For each event interval (event_start, event_end), ensure that either:
#   meeting_end <= event_start  OR  meeting_start >= event_end.
for (event_start, event_end) in all_events:
    s.add(Or(meeting_end <= event_start, meeting_start >= event_end))

# Check for a valid meeting time.
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration

    # Helper function: Convert minutes to HH:MM format.
    def minutes_to_time(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"

    print("A possible meeting time:")
    print(f"Start: {minutes_to_time(start_time)}")
    print(f"End:   {minutes_to_time(end_time)}")
else:
    print("No valid meeting time could be found.")