from z3 import Optimize, Int, Implies, Or

# We'll represent days as integers:
# 0: Monday, 1: Tuesday, 2: Wednesday
# The meeting must start between 9:00 (0 minutes offset) and 16:30 (450 minutes offset)
# Duration is 30 minutes. All times are in minutes offset from 9:00.
meeting_duration = 30

# Create an optimizer so we can use objectives (earliest day and start time)
opt = Optimize()

# Decision variables:
day = Int('day')       # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start = Int('start')   # meeting start offset in minutes from 9:00

# Domain constraints:
# day must be 0,1 or 2,
# start must be at least 0 and meeting must finish by 480 minutes (17:00)
opt.add(day >= 0, day <= 2)
opt.add(start >= 0, start + meeting_duration <= 480)

# Samuel's busy intervals (in minutes offset from 9:00):
# Monday busy intervals:
#   10:30 - 11:00  -> (90, 120)
#   12:00 - 12:30  -> (180, 210)
#   13:00 - 15:00  -> (240, 360)
#   15:30 - 16:30  -> (390, 450)
monday_busy = [(90, 120), (180, 210), (240, 360), (390, 450)]

# Tuesday busy intervals:
#   9:00 - 12:00   -> (0, 180)
#   14:00 - 15:30  -> (300, 390)
#   16:30 - 17:00  -> (450, 480)
tuesday_busy = [(0, 180), (300, 390), (450, 480)]

# Wednesday busy intervals:
#   10:30 - 11:00  -> (90, 120)
#   11:30 - 12:00  -> (150, 180)
#   12:30 - 13:00  -> (210, 240)
#   14:00 - 14:30  -> (300, 330)
#   15:00 - 16:00  -> (360, 420)
wednesday_busy = [(90, 120), (150, 180), (210, 240), (300, 330), (360, 420)]

# For each busy interval for Samuel, if the meeting is on that day we require that
# the meeting does not overlap with the busy interval. Two intervals [s, s+duration] and [b_start, b_end]
# do not overlap if: s + duration <= b_start or s >= b_end.
def add_busy_constraints(day_val, busy_intervals):
    for (bstart, bend) in busy_intervals:
        opt.add(Implies(day == day_val, Or(start + meeting_duration <= bstart, start >= bend)))

# Add constraints for each day:
add_busy_constraints(0, monday_busy)    # Monday
add_busy_constraints(1, tuesday_busy)   # Tuesday
add_busy_constraints(2, wednesday_busy) # Wednesday

# Preferences:
# Larry would rather not meet on Wednesday (day == 2) and Samuel would like to avoid more meetings on Tuesday (day == 1).
# The group prefers the earliest slot. We encode this as an optimization objective minimizing:
#    (day * 10000 + start)
# so that Monday (0) is preferred over Tuesday (1) and Tuesday is preferred over Wednesday (2),
# and for a given day, the earlier start time is chosen.
objective = opt.minimize(day * 10000 + start)

# Check the constraints and get the optimal solution
if opt.check() == 'sat':
    model = opt.model()
    sol_day = model[day].as_long()
    sol_start = model[start].as_long()
    
    # Convert day number to name
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    meeting_day = day_names.get(sol_day, "Unknown")
    
    # Convert meeting start (offset in minutes from 9:00) to HH:MM format
    def minutes_to_time_str(offset):
        total_minutes = 9 * 60 + offset  # since offset is from 9:00
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    meeting_start_time = minutes_to_time_str(sol_start)
    meeting_end_time = minutes_to_time_str(sol_start + meeting_duration)
    
    # Following the required output format:
    print("SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_time}")
    print(f"End Time: {meeting_end_time}")
else:
    print("No solution found.")