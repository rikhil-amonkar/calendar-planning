from z3 import *

solver = Solver()

day = Int('day')
start_time = Int('start_time')

# Day constraints
solver.add(Or(day == 0, day == 1, day == 2, day == 3))

# Time constraints: work hours 9:00-17:00, 30 min meeting
solver.add(start_time >= 9 * 60)  # 540
solver.add(start_time <= 16 * 60 + 30)  # 990

# Julie's preference: if day is Thursday (3), then start_time >= 11:30 (11*60 +30 = 690)
solver.add(If(day == 3, start_time >= 690, True))

# Ruth's availability constraints for days 0, 1, 2
solver.add(If(day == 0, False, True))
solver.add(If(day == 1, False, True))
solver.add(If(day == 2, False, True))

# Ruth's availability constraints for day 3 (Thursday)
# Busy intervals on Thursday: [540, 660), [690, 870), [900, 1020)
# Ensure meeting does not overlap with any of these
solver.add(If(day == 3, Or(start_time + 30 <= 540, 660 <= start_time), True))
solver.add(If(day == 3, Or(start_time + 30 <= 690, 870 <= start_time), True))
solver.add(If(day == 3, Or(start_time + 30 <= 900, 1020 <= start_time), True))

if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_name = days[day_val]
    start_hours = (start_val // 60) % 24
    start_minutes = start_val % 60
    start_time_str = f"{start_hours:02d}:{start_minutes:02d}"
    end_time_val = start_val + 30
    end_hours = (end_time_val // 60) % 24
    end_minutes = end_time_val % 60
    end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found.")