from z3 import *

# Helper functions to convert times.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration
meeting_duration = 30  # half-hour meeting.
work_start = time_to_minutes("9:00")
work_end = time_to_minutes("17:00")

# Megan's preference: avoid meetings before 10:00, so meeting start must be >= 10:00.
preferred_start_for_megan = time_to_minutes("10:00")

# Busy schedules for Monday

# Kimberly's busy intervals.
kimberly_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("12:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Megan has no conflicting meetings (so no intervals).
# Marie's busy intervals.
marie_busy = [
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Diana's busy intervals.
diana_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("14:30")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Set up Z3 solver
s = Solver()

# Define the meeting start time (in minutes) as an integer variable.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: The meeting must be within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint: Satisfy Megan's preference to avoid meetings before 10:00.
s.add(meeting_start >= preferred_start_for_megan)

# Constraint: The meeting should not conflict with Kimberly's busy intervals.
for start, end in kimberly_busy:
    s.add(Or(meeting_end <= start, meeting_start >= end))

# Constraint: The meeting should not conflict with Marie's busy intervals.
for start, end in marie_busy:
    s.add(Or(meeting_end <= start, meeting_start >= end))

# Constraint: The meeting should not conflict with Diana's busy intervals.
for start, end in diana_busy:
    s.add(Or(meeting_end <= start, meeting_start >= end))

# Check for a valid meeting time.
if s.check() == sat:
    model = s.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")