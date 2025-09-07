from z3 import Solver, Int, Or, sat

def minutes_to_timestr(t):
    hours = t // 60
    minutes = t % 60
    return f"{hours:02d}:{minutes:02d}"

# Define the meeting duration (in minutes) and working hours in minutes after midnight
duration = 30
work_start = 9 * 60    # 9:00 -> 540 minutes
work_end = 17 * 60     # 17:00 -> 1020 minutes

# Create a Z3 solver and meeting start variable "m" (in minutes after midnight)
s = Solver()
m = Int('m')

# The meeting must start in the window [work_start, work_end - duration]
s.add(m >= work_start, m <= work_end - duration)

# Busy intervals for each participant (start, end) in minutes after midnight:
busy_intervals = [
    # Joan
    (11 * 60 + 30, 12 * 60),    # 11:30 - 12:00  --> (690, 720)
    (14 * 60 + 30, 15 * 60),    # 14:30 - 15:00  --> (870, 900)
    
    # Megan
    (9 * 60, 10 * 60),          # 9:00 - 10:00    --> (540, 600)
    (14 * 60, 14 * 60 + 30),     # 14:00 - 14:30   --> (840, 870)
    (16 * 60, 16 * 60 + 30),     # 16:00 - 16:30   --> (960, 990)
    
    # Betty
    (9 * 60 + 30, 10 * 60),     # 9:30 - 10:00    --> (570, 600)
    (11 * 60 + 30, 12 * 60),     # 11:30 - 12:00   --> (690, 720)
    (13 * 60 + 30, 14 * 60),     # 13:30 - 14:00   --> (810, 840)
    (16 * 60, 16 * 60 + 30),     # 16:00 - 16:30   --> (960, 990)
    
    # Judith
    (9 * 60, 11 * 60),          # 9:00 - 11:00    --> (540, 660)
    (12 * 60, 13 * 60),         # 12:00 - 13:00   --> (720, 780)
    (14 * 60, 15 * 60),         # 14:00 - 15:00   --> (840, 900)
    
    # Terry
    (9 * 60 + 30, 10 * 60),     # 9:30 - 10:00    --> (570, 600)
    (11 * 60 + 30, 12 * 60 + 30),# 11:30 - 12:30   --> (690, 750)
    (13 * 60, 14 * 60),         # 13:00 - 14:00   --> (780, 840)
    (15 * 60, 15 * 60 + 30),     # 15:00 - 15:30   --> (900, 930)
    (16 * 60, 17 * 60),         # 16:00 - 17:00   --> (960, 1020)
    
    # Kathryn
    (9 * 60 + 30, 10 * 60),     # 9:30 - 10:00    --> (570, 600)
    (10 * 60 + 30, 11 * 60),     # 10:30 - 11:00   --> (630, 660)
    (11 * 60 + 30, 13 * 60),     # 11:30 - 13:00   --> (690, 780)
    (14 * 60, 16 * 60),         # 14:00 - 16:00   --> (840, 960)
    (16 * 60 + 30, 17 * 60)      # 16:30 - 17:00   --> (990, 1020)
]

# For each busy interval, ensure our meeting [m, m+duration] does not overlap.
# That is, for each interval [busy_start, busy_end], either the meeting ends before the busy interval starts
# or it starts after the busy interval ends:
for busy_start, busy_end in busy_intervals:
    s.add(Or(m + duration <= busy_start, m >= busy_end))

# Check for a solution
if s.check() == sat:
    model = s.model()
    start_time = model[m].as_long()
    end_time = start_time + duration
    # Format the output as "Monday HH:MM:HH:MM"
    out_str = f"Monday {minutes_to_timestr(start_time)}:{minutes_to_timestr(end_time)}"
    print(out_str)
else:
    print("No meeting time found")