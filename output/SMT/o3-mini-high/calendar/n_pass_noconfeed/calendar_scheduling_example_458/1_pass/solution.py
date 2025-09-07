from z3 import *

# Meeting duration in minutes
duration = 30

# Define the meeting start time variable t (in minutes after 9:00).
t = Int('t')

solver = Solver()

# Work hours: meeting must finish by 17:00, so t + duration <= 480 minutes (9:00 -> 480 minutes = 17:00).
solver.add(t >= 0, t + duration <= 480)

# Wayne prefers to avoid meetings before 14:00. Since 14:00 is 5 hours after 9:00, t >= 5*60 = 300.
solver.add(t >= 300)

# Define a dictionary of busy intervals for participants.
# The times below are represented in minutes offset from 9:00.
busy_intervals = {
    "Melissa": [(60, 120),    # 10:00 to 11:00
                (210, 300),   # 12:30 to 14:00
                (360, 390)],  # 15:00 to 15:30
    "Gregory": [(210, 240),   # 12:30 to 13:00
                (390, 420)],  # 15:30 to 16:00
    "Victoria": [(0, 30),      # 9:00 to 9:30
                 (90, 150),    # 10:30 to 11:30
                 (240, 300),   # 13:00 to 14:00
                 (330, 360),   # 14:30 to 15:00
                 (390, 450)],  # 15:30 to 16:30
    "Thomas": [(60, 180),      # 10:00 to 12:00
               (210, 240),     # 12:30 to 13:00
               (330, 420)],    # 14:30 to 16:00
    "Jennifer": [(0, 30),      # 9:00 to 9:30
                 (60, 90),     # 10:00 to 10:30
                 (120, 240),   # 11:00 to 13:00
                 (270, 330),   # 13:30 to 14:30
                 (360, 390),   # 15:00 to 15:30
                 (420, 450)]   # 16:00 to 16:30
    # Wayne and Catherine are free (except Wayne's meeting preference already added).
}

# For each busy interval, ensure that the meeting [t, t+duration] does NOT overlap.
# Two intervals [a, b] and [c, d] do not overlap if either b <= c or a >= d.
for person, intervals in busy_intervals.items():
    for (busy_start, busy_end) in intervals:
        solver.add(Or(t + duration <= busy_start, t >= busy_end))

# Check if a solution exists.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[t].as_long()  # in minutes after 9:00
    meeting_end = meeting_start + duration

    # Function to convert minutes into HH:MM format (using the real clock from 9:00)
    def convert_time(minutes_offset):
        total_minutes = 9 * 60 + minutes_offset  # 9:00 in minutes + offset
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    start_str = convert_time(meeting_start)
    end_str = convert_time(meeting_end)
    
    # Output the day and time range in the format: "Day HH:MM:HH:MM"
    print(f"Monday {start_str}:{end_str}")
else:
    print("No available meeting time found.")