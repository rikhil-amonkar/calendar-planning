from z3 import Solver, Int, Or, sat

# Define the meeting duration (in minutes)
meeting_duration = 30

# meeting_start is the start time in minutes from midnight.
# Workday is Monday 9:00 (540) to 17:00 (1020), but Billy prefers no meetings after 15:00.
meeting_start = Int('meeting_start')
meeting_end = meeting_start + meeting_duration

solver = Solver()

# Global constraints:
# Meeting must start no earlier than 9:00 and finish by 17:00.
solver.add(meeting_start >= 540)       # 9:00 AM
solver.add(meeting_end <= 1020)        # 17:00 (5:00 PM)
# Billy's preference: no meetings after 15:00 (i.e., meeting must finish by 15:00).
solver.add(meeting_end <= 900)         # 15:00 (3:00 PM)

# Helper to assert that the meeting does not overlap a busy interval.
def no_overlap(busy_start, busy_end):
    # Meeting is non-overlapping with a busy interval if it ends before the busy period starts
    # or starts after the busy period ends. Equality is allowed.
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Raymond's busy intervals on Monday: (in minutes from midnight)
# 9:00-9:30, 11:30-12:00, 13:00-13:30, 15:00-15:30
busy_raymond = [
    (540, 570),
    (690, 720),
    (780, 810),
    (900, 930)
]

# Billy's busy intervals on Monday:
# 10:00-10:30, 12:00-13:00, 16:30-17:00
busy_billy = [
    (600, 630),
    (720, 780),
    (990, 1020)
]

# Donald's busy intervals on Monday:
# 9:00-9:30, 10:00-11:00, 12:00-13:00, 14:00-14:30, 16:00-17:00
busy_donald = [
    (540, 570),
    (600, 660),
    (720, 780),
    (840, 870),
    (960, 1020)
]

# Add constraints for Raymond's busy times
for start, end in busy_raymond:
    solver.add(no_overlap(start, end))

# Add constraints for Billy's busy times
for start, end in busy_billy:
    solver.add(no_overlap(start, end))

# Add constraints for Donald's busy times
for start, end in busy_donald:
    solver.add(no_overlap(start, end))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration

    # Function to convert minutes from midnight to HH:MM string format.
    def minutes_to_time(m):
        hour = m // 60
        minute = m % 60
        return f"{hour:02d}:{minute:02d}"

    start_str = minutes_to_time(start_val)
    end_str = minutes_to_time(end_val)

    print("Monday")
    print(f"{start_str}:{end_str}")
else:
    print("No valid meeting time found.")