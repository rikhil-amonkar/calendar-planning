from z3 import *

# Create the solver
s = Solver()

# Define the meeting start time in minutes from midnight (integer)
m = Int('m')
duration = 30

# Working day boundaries in minutes (9:00 to 17:00)
start_work = 9 * 60   # 540 minutes
end_work = 17 * 60    # 1020 minutes

# Melissa's preference: meeting should finish by 14:00 (840 minutes)
end_preferred = 14 * 60  # 840 minutes

# Basic domain constraints: meeting must start within work hours and finish by 17:00
s.add(m >= start_work, m + duration <= end_work)

# Enforce Melissa's preference: meeting must finish by 14:00
s.add(m + duration <= end_preferred)

# For any busy interval [busy_start, busy_end), 
# we require that the meeting [m, m+duration) does not intersect it.
# This is expressed as: (m + duration <= busy_start) or (m >= busy_end)

# Jeffrey's busy intervals on Monday:
#  9:30 to 10:00 -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
s.add(Or(m + duration <= 570, m >= 600))
s.add(Or(m + duration <= 630, m >= 660))

# Virginia's busy intervals on Monday:
#  9:00 to 9:30 -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
s.add(Or(m + duration <= 540, m >= 570))
s.add(Or(m + duration <= 600, m >= 630))
s.add(Or(m + duration <= 870, m >= 900))
s.add(Or(m + duration <= 960, m >= 990))

# Melissa's busy intervals on Monday:
#  9:00 to 11:30 -> [540, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 15:00 -> [780, 900)
# 16:00 to 17:00 -> [960, 1020)
s.add(Or(m + duration <= 540, m >= 690))
s.add(Or(m + duration <= 720, m >= 750))
s.add(Or(m + duration <= 780, m >= 900))
s.add(Or(m + duration <= 960, m >= 1020))

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    meeting_start = model[m].as_long()
    meeting_end = meeting_start + duration

    # Helper to convert minutes into HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    
    print(f"Monday {start_str}:{end_str}")
else:
    print("No solution found")