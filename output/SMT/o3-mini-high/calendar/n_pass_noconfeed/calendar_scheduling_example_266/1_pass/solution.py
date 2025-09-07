from z3 import Int, Solver, Or, sat

# Meeting parameters
meeting_duration = 30  # in minutes
work_start = 9 * 60    # 9:00 AM in minutes (540)
work_end = 17 * 60     # 17:00 (5:00 PM) in minutes (1020)

# Create a Z3 integer variable representing the start time (in minutes)
start = Int('start')

solver = Solver()

# Constraint: meeting must be within work hours
solver.add(start >= work_start, start + meeting_duration <= work_end)

# Define busy intervals for each participant as (start, end) in minutes
busy_intervals = [
    # Joe's busy times: 9:30-10:00 and 10:30-11:00
    (9 * 60 + 30, 10 * 60),       # (570, 600)
    (10 * 60 + 30, 11 * 60),      # (630, 660)
    
    # Keith's busy times: 11:30-12:00 and 15:00-15:30
    (11 * 60 + 30, 12 * 60),      # (690, 720)
    (15 * 60, 15 * 60 + 30),      # (900, 930)
    
    # Patricia's busy times: 9:00-9:30 and 13:00-13:30
    (9 * 60, 9 * 60 + 30),        # (540, 570)
    (13 * 60, 13 * 60 + 30),      # (780, 810)
    
    # Nancy's busy times: 9:00-11:00 and 11:30-16:30
    (9 * 60, 11 * 60),            # (540, 660)
    (11 * 60 + 30, 16 * 60 + 30),  # (690, 990)
    
    # Pamela's busy times:
    (9 * 60, 10 * 60),            # 9:00-10:00  -> (540, 600)
    (10 * 60 + 30, 11 * 60),       # 10:30-11:00 -> (630, 660)
    (11 * 60 + 30, 12 * 60 + 30),  # 11:30-12:30 -> (690, 750)
    (13 * 60, 14 * 60),           # 13:00-14:00 -> (780, 840)
    (14 * 60 + 30, 15 * 60),       # 14:30-15:00 -> (870, 900)
    (15 * 60 + 30, 16 * 60),       # 15:30-16:00 -> (930, 960)
    (16 * 60 + 30, 17 * 60)        # 16:30-17:00 -> (990, 1020)
]

# For each busy interval, ensure the meeting [start, start+30) does NOT overlap.
# This condition can be expressed as: 
# either the meeting ends at or before the busy interval starts,
# or it starts at or after the busy interval ends.
for b_start, b_end in busy_intervals:
    solver.add(Or(start + meeting_duration <= b_start, start >= b_end))

# Check if there is a solution that satisfies all constraints.
if solver.check() == sat:
    model = solver.model()
    start_time = model[start].as_long()
    end_time = start_time + meeting_duration
    
    # Convert minutes to HH:MM format
    def format_time(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    meeting_range = f"{format_time(start_time)}:{format_time(end_time)}"
    day_of_week = "Monday"
    
    print(f"Meeting Time: {{{meeting_range}}}, Day: {day_of_week}")
else:
    print("No valid meeting time found.")