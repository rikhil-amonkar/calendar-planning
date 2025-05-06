from z3 import *

# Helper functions
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration
meeting_duration = 30  # half an hour meeting
work_start = time_to_minutes("9:00")    # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# Participants' schedules (Monday):
# Judy is free all day, so no busy intervals.
# Nicole's busy intervals on Monday.
nicole_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("16:30"))
]

# Nicole would rather not meet on Monday before 16:00.
# We enforce that the meeting must start no earlier than 16:00.
preferred_start = time_to_minutes("16:00")

# Create a Z3 Solver instance 
s = Solver()

# Declare an integer variable for the meeting start time (in minutes)
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: The meeting must be within work hours (9:00 to 17:00)
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint 2: Honor Nicole's preference: meeting should not start before 16:00.
s.add(meeting_start >= preferred_start)

# Constraint 3: The meeting must not overlap any busy interval of Nicole.
# For each busy interval, the meeting either must finish before the busy period starts
# or start after the busy period ends.
for busy_start, busy_end in nicole_busy:
    s.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Check for a valid solution
if s.check() == sat:
    model = s.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")