from z3 import *

# Define participants' busy times in minutes since 9:00 for each day
bobby = {
    0: [(330, 360)],  # Monday: 14:30-15:00
    1: [(0, 150), (180, 210), (240, 360), (390, 480)]  # Tuesday
}

michael = {
    0: [(0, 60), (90, 270), (300, 360), (390, 480)],  # Monday
    1: [(0, 90), (120, 150), (180, 300), (360, 420), (450, 480)]  # Tuesday
}

# Create variables
day = Int('day')
start_time = Int('start_time')

# Initialize optimizer
opt = Optimize()

# Day constraints (0 for Monday, 1 for Tuesday)
opt.add(Or(day == 0, day == 1))

# Meeting must be within 9:00-17:00 (480 minutes)
opt.add(start_time >= 0)
opt.add(start_time + 30 <= 480)

# Add constraints for Bobby's availability
for d in [0, 1]:
    for (s, e) in bobby[d]:
        opt.add(Implies(day == d, Or(start_time + 30 <= s, start_time >= e)))

# Add constraints for Michael's availability
for d in [0, 1]:
    for (s, e) in michael[d]:
        opt.add(Implies(day == d, Or(start_time + 30 <= s, start_time >= e)))

# Minimize to find earliest possible time (prioritize day then start time)
opt.minimize(day * 1000 + start_time)

# Solve and output
if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    s = m[start_time].as_long()
    day_str = "Monday" if d == 0 else "Tuesday"
    start_h = 9 + s // 60
    start_m = s % 60
    end_time = s + 30
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    print(f"Day: {day_str}, Start: {start_h:02}:{start_m:02}, End: {end_h:02}:{end_m:02}")
else:
    print("No solution found")