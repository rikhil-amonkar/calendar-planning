from z3 import Solver, Int, Or

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration.
meeting_duration = 30  # 30 minutes meeting.
work_start = time_to_minutes("9:00")   # 540 minutes.
work_end   = time_to_minutes("17:00")  # 1020 minutes.

# Busy intervals for each participant on Monday (in minutes).
# Each tuple represents (start_time, end_time) of a busy slot.

# Walter is free all day, so no busy intervals.
cynthia_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("16:00"))
]

ann_busy = [
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

catherine_busy = [
    (time_to_minutes("9:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("17:00"))
]

kyle_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("16:00"))
]

# Create a Z3 solver.
solver = Solver()

# Define the meeting start time variable in minutes.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: Meeting must start and finish within work hours.
solver.add(meeting_start >= work_start)
solver.add(meeting_end <= work_end)

# Helper function to add non-overlap constraint for a list of busy intervals.
def add_busy_constraints(busy_intervals):
    for (busy_start, busy_end) in busy_intervals:
        # Meeting must either finish before the busy interval starts, or start after it ends.
        solver.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add busy constraints for Cynthia, Ann, Catherine and Kyle.
add_busy_constraints(cynthia_busy)
add_busy_constraints(ann_busy)
add_busy_constraints(catherine_busy)
add_busy_constraints(kyle_busy)

# Check for a valid meeting time.
if solver.check() == 'sat' or solver.check() is not None:
    model = solver.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")