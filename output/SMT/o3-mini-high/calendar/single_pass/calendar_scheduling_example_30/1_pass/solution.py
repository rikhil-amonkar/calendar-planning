from z3 import *

# Convert a time given in minutes relative to 9:00 into HH:MM format.
def minutes_to_time(m):
    total_minutes = m + (9 * 60)  # 9:00 is the base start of the day
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting parameters
duration = 30    # 30-minute meeting
work_start = 0   # 9:00 relative as 0
work_end = 480   # 17:00 relative as 480 minutes (9:00 to 17:00 -> 8 hours * 60)
# Melissa's preference: No meeting after 14:00 means the meeting must finish by 14:00.
melissa_latest_end = 300  # since 14:00 is 5 hours after 9:00, i.e. 300 minutes

s = Solver()
# Meeting start time, in minutes relative to 9:00 (0 means 9:00, 150 means 11:30, etc.)
start = Int('start')

# The meeting must occur within working hours
s.add(start >= work_start)
s.add(start + duration <= work_end)
# Apply Melissa's preference: the meeting must finish by 14:00
s.add(start + duration <= melissa_latest_end)

# Helper function: Given a busy interval [busy_start, busy_end) for a participant,
# the meeting must either finish before that busy interval or start after it.
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Jeffrey's busy intervals on Monday (times are relative to 9:00):
# 9:30-10:00 -> [30, 60)
# 10:30-11:00 -> [90, 120)
s.add(non_overlap(30, 60))
s.add(non_overlap(90, 120))

# Virginia's busy intervals on Monday:
# 9:00-9:30 -> [0, 30)
# 10:00-10:30 -> [60, 90)
# 14:30-15:00 -> [330, 360)
# 16:00-16:30 -> [420, 450)
s.add(non_overlap(0, 30))
s.add(non_overlap(60, 90))
s.add(non_overlap(330, 360))
s.add(non_overlap(420, 450))

# Melissa's busy intervals on Monday:
# 9:00-11:30 -> [0, 150)
# 12:00-12:30 -> [180, 210)
# 13:00-15:00 -> [240, 360)
# 16:00-17:00 -> [420, 480)
s.add(non_overlap(0, 150))
s.add(non_overlap(180, 210))
s.add(non_overlap(240, 360))
s.add(non_overlap(420, 480))

if s.check() == sat:
    model = s.model()
    sol_start = model[start].as_long()
    sol_end = sol_start + duration
    # Convert the relative minutes back to the HH:MM format (adding the 9:00 base).
    start_time_str = minutes_to_time(sol_start)
    end_time_str = minutes_to_time(sol_end)
    
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: " + start_time_str)
    print("End Time: " + end_time_str)
else:
    print("No solution found")