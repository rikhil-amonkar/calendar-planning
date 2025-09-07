from z3 import *

# Convert a time in "HH:MM" to minutes since midnight
def to_minutes(hour, minute):
    return hour * 60 + minute

# Define the meeting duration in minutes and working hours (9AM to 5PM)
meeting_duration = 30
work_start = to_minutes(9, 0)
work_end = to_minutes(17, 0)  # meeting must finish by 17:00

# Create the Z3 solver instance
solver = Solver()

# Define the meeting start time variable (in minutes since midnight)
meeting_start = Int("meeting_start")

# The meeting must start within the working interval such that it finishes by work_end
solver.add(meeting_start >= work_start)
solver.add(meeting_start + meeting_duration <= work_end)

# Helper function: no_overlap constraint for a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end):
    # The meeting must either finish before the busy interval starts
    # or start after the busy interval ends.
    return Or(meeting_start + meeting_duration <= busy_start,
              meeting_start >= busy_end)

# Participant schedules for Monday (all times in minutes since midnight):

# Eric: No meetings, so no extra constraints.

# Ashley's busy intervals:
# 10:00 to 10:30, 11:00 to 12:00, 12:30 to 13:00, 15:00 to 16:00
ashley_intervals = [
    (to_minutes(10, 0), to_minutes(10, 30)),
    (to_minutes(11, 0), to_minutes(12, 0)),
    (to_minutes(12, 30), to_minutes(13, 0)),
    (to_minutes(15, 0), to_minutes(16, 0)),
]
for busy_start, busy_end in ashley_intervals:
    solver.add(no_overlap(busy_start, busy_end))

# Ronald's busy intervals:
# 9:00 to 9:30, 10:00 to 11:30, 12:30 to 14:00, 14:30 to 17:00
ronald_intervals = [
    (to_minutes(9, 0), to_minutes(9, 30)),
    (to_minutes(10, 0), to_minutes(11, 30)),
    (to_minutes(12, 30), to_minutes(14, 0)),
    (to_minutes(14, 30), to_minutes(17, 0)),
]
for busy_start, busy_end in ronald_intervals:
    solver.add(no_overlap(busy_start, busy_end))

# Larry's busy intervals:
# 9:00 to 12:00, 13:00 to 17:00
larry_intervals = [
    (to_minutes(9, 0), to_minutes(12, 0)),
    (to_minutes(13, 0), to_minutes(17, 0)),
]
for busy_start, busy_end in larry_intervals:
    solver.add(no_overlap(busy_start, busy_end))

# Solve for a meeting start time that satisfies all constraints
if solver.check() == sat:
    model = solver.model()
    start = model[meeting_start].as_long()
    end = start + meeting_duration
    
    # Function to format minutes into HH:MM string
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    # The meeting is scheduled on Monday
    day = "Monday"
    meeting_time_str = f"{format_time(start)}:{format_time(end)}"
    
    print(day)
    print(meeting_time_str)
else:
    print("No solution found.")