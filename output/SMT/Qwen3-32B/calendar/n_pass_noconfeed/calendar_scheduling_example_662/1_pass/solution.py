from z3 import *

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

s = Solver()

day = Int('day')
start_time = Int('start_time')

# Day must be 0 (Monday) or 1 (Tuesday)
s.add(Or(day == 0, day == 1))

# Time must be between 9:00 (540) and 17:00 (1020) minus 60 minutes (so start_time <= 960)
s.add(And(start_time >= 540, start_time <= 960))

# Blocked intervals for each day and participant
mon_g_blocked = [(570, 600), (660, 780), (840, 870), (990, 1020)]
mon_d_blocked = [(540, 570), (600, 780), (870, 990)]
mon_blocked = mon_g_blocked + mon_d_blocked

tue_g_blocked = [(540, 570), (630, 660), (870, 960)]
tue_d_blocked = [(540, 570), (600, 630), (660, 750), (780, 870), (900, 960), (990, 1020)]
tue_blocked = tue_g_blocked + tue_d_blocked

# Constraints for Monday
mon_overlap_constraints = And([Or(start_time + 60 <= b_start, start_time >= b_end) for (b_start, b_end) in mon_blocked])
# Constraints for Tuesday
tue_overlap_constraints = And([Or(start_time + 60 <= b_start, start_time >= b_end) for (b_start, b_end) in tue_blocked])

# Add implications based on day
s.add(Implies(day == 0, mon_overlap_constraints))
s.add(Implies(day == 1, tue_overlap_constraints))

if s.check() == sat:
    model = s.model()
    day_val = model[day].as_long()
    start = model[start_time].as_long()
    end = start + 60
    day_str = "Monday" if day_val == 0 else "Tuesday"
    start_str = minutes_to_time(start)
    end_str = minutes_to_time(end)
    print(f"{start_str}:{end_str} {day_str}")
else:
    print("No solution found.")