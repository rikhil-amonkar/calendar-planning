from z3 import *

# Helper: Convert "HH:MM" strings into minutes past midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

# Meeting configuration: Duration is 30 minutes.
meeting_duration = 30

# Work hours on Monday (9:00 to 17:00).
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# Jack's busy intervals on Monday.
jack_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Charlotte's busy intervals on Monday.
charlotte_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:00"))
]

# Jack prefers to avoid meetings after 12:30, so the meeting must finish by then.
latest_end_for_jack = time_to_minutes("12:30")

# Combine all busy intervals from both participants.
all_busy = jack_busy + charlotte_busy

# Create Z3 solver.
s = Solver()

# meeting_start: the meeting's start time (in minutes after midnight).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: The meeting must be within work hours.
s.add(meeting_start >= work_start)
s.add(meeting_end <= work_end)

# Constraint 2: Jack prefers not to have meetings after 12:30.
s.add(meeting_end <= latest_end_for_jack)

# Constraint 3: The meeting must not overlap any busy interval.
# For each busy interval, either meeting ends before it starts or starts after it ends.
for (busy_start, busy_end) in all_busy:
    s.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Find and print a valid meeting time.
if s.check() == sat:
    model = s.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration

    # Helper: Convert minutes back to "HH:MM" format.
    def minutes_to_time(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"

    print("A possible meeting time on Monday:")
    print(f"Start: {minutes_to_time(start_val)}")
    print(f"End:   {minutes_to_time(end_val)}")
else:
    print("No valid meeting time could be found.")