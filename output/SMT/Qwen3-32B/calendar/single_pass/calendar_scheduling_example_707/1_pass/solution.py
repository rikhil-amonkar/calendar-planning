from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

day = Int('day')
start = Int('start')

# Day must be 0 (Monday) or 1 (Tuesday)
solver.add(Or(day == 0, day == 1))
# Start time between 9:00 (540) and 16:30 (990)
solver.add(start >= 540)
solver.add(start <= 990)

# Ryan's Monday and Tuesday busy intervals
ryan_mon = [(570, 600), (660, 720), (780, 810), (930, 960)]
ryan_tue = [(750, 810), (930, 960)]
# Adam's Monday and Tuesday busy intervals
adam_mon = [(540, 630), (660, 810), (840, 960), (990, 1020)]
adam_tue = [(540, 590), (630, 930), (960, 1020)]

# Add constraints for Ryan's Monday
for (bs, be) in ryan_mon:
    solver.add(Or(day != 0, Or(start >= be, start + 30 <= bs)))

# Add constraints for Ryan's Tuesday
for (bs, be) in ryan_tue:
    solver.add(Or(day != 1, Or(start >= be, start + 30 <= bs)))

# Add constraints for Adam's Monday
for (bs, be) in adam_mon:
    solver.add(Or(day != 0, Or(start >= be, start + 30 <= bs)))

# Add constraints for Adam's Tuesday
for (bs, be) in adam_tue:
    solver.add(Or(day != 1, Or(start >= be, start + 30 <= bs)))

if solver.check() == sat:
    model = solver.model()
    day_val = model.eval(day).as_long()
    start_val = model.eval(start).as_long()
    end_val = start_val + 30

    day_str = "Monday" if day_val == 0 else "Tuesday"
    start_time = minutes_to_time(start_val)
    end_time = minutes_to_time(end_val)

    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found")