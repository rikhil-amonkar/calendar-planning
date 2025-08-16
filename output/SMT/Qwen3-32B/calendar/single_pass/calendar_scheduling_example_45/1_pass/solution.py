from z3 import *

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

# Define blocked intervals for Samuel in minutes since midnight
blocked = [
    (540, 630),   # 9:00-10:30
    (690, 720),   # 11:30-12:00
    (780, 810),   # 13:00-13:30
    (840, 960),   # 14:00-16:00
    (990, 1020),  # 16:30-17:00
]

opt = Optimize()

start_time = Int('start_time')

# Constraints for overall working hours (9:00-17:00)
opt.add(start_time >= 540)
opt.add(start_time <= 990)  # since 990 +30 = 1020 (17:00)

# Constraints for Samuel's blocked times
for block_start, block_end in blocked:
    opt.add(Or(start_time + 30 <= block_start, start_time >= block_end))

# Minimize the start time for earliest availability
opt.minimize(start_time)

if opt.check() == sat:
    model = opt.model()
    start = model[start_time].as_long()
    end = start + 30
    day = "Monday"
    start_str = minutes_to_time(start)
    end_str = minutes_to_time(end)
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")
else:
    print("No solution found")