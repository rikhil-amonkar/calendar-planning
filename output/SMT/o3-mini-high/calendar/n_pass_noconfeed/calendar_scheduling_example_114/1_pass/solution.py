from z3 import *

def minutes_to_time(minutes):
    # Convert minutes (offset from 9:00) into HH:MM format (24-hour clock)
    total = minutes + 9 * 60  # 9:00 AM as the reference
    hour = total // 60
    minute = total % 60
    return f"{hour:02d}:{minute:02d}"

# Meeting duration in minutes
duration = 60

# Working hours: meeting must be scheduled between 9:00 and 17:00.
# We represent meeting_start as minutes offset from 9:00. Hence, meeting_start >= 0 and meeting_start + duration <= 480.
meeting_start = Int('meeting_start')
meeting_end = meeting_start + duration

solver = Solver()

# Constraint: Meeting must be within work hours (9:00 to 17:00)
solver.add(meeting_start >= 0, meeting_end <= 480)

# Busy intervals for each participant (as minutes offset from 9:00)
# Format: (busy_start, busy_end)
busy_intervals = [
    # Stephanie: busy 10:00-10:30 and 16:00-16:30
    (60, 90),
    (420, 450),
    # Cheryl: busy 10:00-10:30, 11:30-12:00, 13:30-14:00, 16:30-17:00
    (60, 90),
    (150, 180),
    (270, 300),
    (450, 480),
    # Bradley: busy 9:30-10:00, 10:30-11:30, 13:30-14:00, 14:30-15:00, 15:30-17:00
    (30, 60),
    (90, 150),
    (270, 300),
    (330, 360),
    (390, 480),
    # Steven: busy 9:00-12:00, 13:00-13:30, 14:30-17:00
    (0, 180),
    (240, 270),
    (330, 480)
]

# For each busy interval, add a constraint to ensure that the meeting does not overlap the busy block.
# That is, either the meeting ends on or before a busy block starts,
# or it starts on or after the busy block ends.
for busy_start, busy_end in busy_intervals:
    solver.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + duration
    
    # Convert offsets to HH:MM
    start_str = minutes_to_time(start_val)
    end_str = minutes_to_time(end_val)
    
    meeting_time_str = f"{start_str}:{end_str}"
    day_of_week = "Monday"
    
    print(f"Proposed meeting time: {meeting_time_str} on {day_of_week}")
else:
    print("No valid meeting time found.")