from z3 import *

def minutes_to_time(minutes):
    # Convert minutes (offset from 9:00) to actual hour and minute
    total = 9 * 60 + minutes
    hour = total // 60
    minute = total % 60
    return hour, minute

# Create the solver
s = Solver()

# Meeting start time (in minutes offset from 9:00)
m = Int('m')
meeting_duration = 30

# Working hours: 9:00 to 17:00 so m must be between 0 and 480-30 = 450 minutes.
s.add(m >= 0, m <= 450)

# Busy intervals for each participant (expressed in minutes offset from 9:00)
busy_intervals = [
    # Cynthia's busy intervals: 9:00-9:30, 10:00-10:30, 13:30-14:30, 15:00-16:00
    (0, 30),
    (60, 90),
    (270, 330),
    (360, 420),
    
    # Ann's busy intervals: 10:00-11:00, 13:00-13:30, 14:00-15:00, 16:00-16:30
    (60, 120),
    (240, 270),
    (300, 360),
    (420, 450),

    # Catherine's busy intervals: 9:00-11:30, 12:30-13:30, 14:30-17:00
    (0, 150),
    (210, 270),
    (330, 480),

    # Kyle's busy intervals: 9:00-9:30, 10:00-11:30, 12:00-12:30, 13:00-14:30, 15:00-16:00
    (0, 30),
    (60, 150),
    (180, 210),
    (240, 330),
    (360, 420)
]

# For each busy interval, ensure the meeting [m, m+meeting_duration) does not overlap.
for start_busy, end_busy in busy_intervals:
    s.add(Or(m + meeting_duration <= start_busy, m >= end_busy))

if s.check() == sat:
    model = s.model()
    meeting_start = model[m].as_long()
    meeting_end = meeting_start + meeting_duration
    start_hour, start_min = minutes_to_time(meeting_start)
    end_hour, end_min = minutes_to_time(meeting_end)
    # Output in the format HH:MM:HH:MM along with the day of the week.
    print(f"Monday {start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}")
else:
    print("No valid meeting time found.")