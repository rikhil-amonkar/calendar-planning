from z3 import *

# Define meeting parameters
meeting_duration = 30  # minutes
work_start = 9 * 60    # 9:00 in minutes (540)
work_end = 17 * 60     # 17:00 in minutes (1020)

# Define the meeting start time variable (in minutes from midnight)
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Create solver and add work hour constraints:
solver = Solver()
solver.add(meeting_start >= work_start)
solver.add(meeting_end <= work_end)

# Busy intervals in minutes from midnight for each participant
# Format: (busy_start, busy_end)
busy_intervals = [
    # Stephanie's busy intervals
    (11 * 60, 11 * 60 + 30),   # 11:00 to 11:30 -> (660, 690)
    (14 * 60 + 30, 15 * 60),    # 14:30 to 15:00 -> (870, 900)
    
    # Joe's busy intervals
    (9 * 60, 9 * 60 + 30),      # 9:00 to 9:30 -> (540, 570)
    (10 * 60, 12 * 60),         # 10:00 to 12:00 -> (600, 720)
    (12 * 60 + 30, 13 * 60),    # 12:30 to 13:00 -> (750, 780)
    (14 * 60, 17 * 60),         # 14:00 to 17:00 -> (840, 1020)
    
    # Diana's busy intervals
    (9 * 60, 10 * 60 + 30),     # 9:00 to 10:30 -> (540, 630)
    (11 * 60 + 30, 12 * 60),    # 11:30 to 12:00 -> (690, 720)
    (13 * 60, 14 * 60),         # 13:00 to 14:00 -> (780, 840)
    (14 * 60 + 30, 15 * 60 + 30),# 14:30 to 15:30 -> (870, 930)
    (16 * 60, 17 * 60),         # 16:00 to 17:00 -> (960, 1020)
    
    # Deborah's busy intervals
    (9 * 60, 10 * 60),          # 9:00 to 10:00 -> (540, 600)
    (10 * 60 + 30, 12 * 60),    # 10:30 to 12:00 -> (630, 720)
    (12 * 60 + 30, 13 * 60),    # 12:30 to 13:00 -> (750, 780)
    (13 * 60 + 30, 14 * 60),    # 13:30 to 14:00 -> (810, 840)
    (14 * 60 + 30, 15 * 60 + 30),# 14:30 to 15:30 -> (870, 930)
    (16 * 60, 16 * 60 + 30)     # 16:00 to 16:30 -> (960, 990)
]

# For each busy interval, ensure the meeting does not overlap:
for busy_start, busy_end in busy_intervals:
    solver.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Solve and print the meeting time
if solver.check() == sat:
    model = solver.model()
    start = model[meeting_start].as_long()
    end = start + meeting_duration

    # Convert minutes to HH:MM format
    start_hour = start // 60
    start_min = start % 60
    end_hour = end // 60
    end_min = end % 60

    # Output the meeting time range and day (Monday)
    print(f"{start_hour:02}:{start_min:02}:{end_hour:02}:{end_min:02} Monday")
else:
    print("No available meeting time found.")