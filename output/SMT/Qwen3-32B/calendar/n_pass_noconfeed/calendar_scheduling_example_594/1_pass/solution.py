from z3 import *

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

opt = Optimize()

start = Int('start')

# Workday is from 9:00 (540) to 17:00 (1020)
opt.add(And(start >= 540, start <= 990))  # start + 30 <= 1020 → start <= 990

# Adam's busy intervals in minutes
adam_busy = [
    (570, 600),  # 9:30-10:00
    (750, 780),  # 12:30-13:00
    (870, 900),  # 14:30-15:00
    (990, 1020)  # 16:30-17:00
]

# Roy's busy intervals in minutes
roy_busy = [
    (600, 660),  # 10:00-11:00
    (690, 780),  # 11:30-13:00
    (810, 870),  # 13:30-14:30
    (990, 1020)  # 16:30-17:00
]

# Add constraints for Adam's busy times
for s, e in adam_busy:
    opt.add(Or(start + 30 <= s, start >= e))

# Add constraints for Roy's busy times
for s, e in roy_busy:
    opt.add(Or(start + 30 <= s, start >= e))

# Minimize the start time
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    start_val = model[start].as_long()
    start_time = minutes_to_time(start_val)
    end_time = minutes_to_time(start_val + 30)
    print(f"{start_time}:{end_time} Monday")
else:
    print("No solution found.")