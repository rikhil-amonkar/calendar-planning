from z3 import *

# Helper functions for time conversion.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration.
meeting_duration = 30  # in minutes
work_start = time_to_minutes("9:00")    # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# Busy intervals for each participant on Monday:
# Intervals are represented as (start, end) in minutes.

# Gregory's busy intervals.
gregory_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00"))
]

# Natalie is free all day so no intervals needed.
natalie_busy = []

# Christine's busy intervals.
christine_busy = [
    (time_to_minutes("9:00"), time_to_minutes("11:30")),
    (time_to_minutes("13:30"), time_to_minutes("17:00"))
]

# Vincent's busy intervals.
vincent_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("17:00"))
]

# Create Z3 solver.
s = Solver()

# Define the meeting start time (in minutes) as an integer variable.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: Meeting must be scheduled within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint 2: The meeting must not overlap any participant's busy intervals.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        s.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add constraints for each participant.
add_busy_constraints(gregory_busy)
add_busy_constraints(natalie_busy)
add_busy_constraints(christine_busy)
add_busy_constraints(vincent_busy)

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