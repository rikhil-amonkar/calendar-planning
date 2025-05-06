from z3 import Solver, Int, Or

# Helper functions for converting time strings to minutes and vice versa.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# Busy intervals for each participant on Monday (in minutes).
# Each participant's busy intervals is a list of tuples (start, end).

gregory_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00"))
]

jonathan_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

barbara_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00"))
]

jesse_busy = [
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("12:30"), time_to_minutes("14:30"))
]

alan_busy = [
    (time_to_minutes("9:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

nicole_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("17:00"))
]

catherine_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Create a Z3 solver instance.
solver = Solver()

# Define the meeting start time variable (in minutes).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: The meeting must be within work hours.
solver.add(meeting_start >= work_start, meeting_end <= work_end)

# For a given busy interval [busy_start, busy_end], the meeting must not overlap:
#   meeting_end <= busy_start  or  meeting_start >= busy_end
def add_busy_constraints(busy_intervals):
    for (busy_start, busy_end) in busy_intervals:
        solver.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add constraints for each participant.
add_busy_constraints(gregory_busy)
add_busy_constraints(jonathan_busy)
add_busy_constraints(barbara_busy)
add_busy_constraints(jesse_busy)
add_busy_constraints(alan_busy)
add_busy_constraints(nicole_busy)
add_busy_constraints(catherine_busy)

# Check for a valid meeting time.
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")