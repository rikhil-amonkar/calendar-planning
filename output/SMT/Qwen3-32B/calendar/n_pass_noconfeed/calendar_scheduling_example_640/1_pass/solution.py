from z3 import *

def to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

# Define busy intervals
bobby_mon = [(870, 900)]
michael_mon = [(540, 600), (630, 810), (840, 900), (930, 1020)]
bobby_tue = [(540, 690), (720, 750), (780, 900), (930, 1020)]
michael_tue = [(540, 630), (660, 690), (720, 840), (900, 960), (990, 1020)]

day = Int('day')
start = Int('start')

opt = Optimize()

# Day must be 0 (Monday) or 1 (Tuesday)
opt.add(Or(day == 0, day == 1))

# Start time must be between 9:00 (540) and 17:00 - 30 min (990)
opt.add(And(start >= 540, start <= 990))

# Monday constraints for Bobby
for s, e in bobby_mon:
    opt.add(Implies(day == 0, Or(start + 30 <= s, start >= e)))

# Monday constraints for Michael
for s, e in michael_mon:
    opt.add(Implies(day == 0, Or(start + 30 <= s, start >= e)))

# Tuesday constraints for Bobby
for s, e in bobby_tue:
    opt.add(Implies(day == 1, Or(start + 30 <= s, start >= e)))

# Tuesday constraints for Michael
for s, e in michael_tue:
    opt.add(Implies(day == 1, Or(start + 30 <= s, start >= e)))

# Minimize the start time
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 30
    days = ['Monday', 'Tuesday']
    start_time = to_time(start_val)
    end_time = to_time(end_val)
    print(f"{days[day_val]} {start_time}:{end_time}")
else:
    print("No solution")