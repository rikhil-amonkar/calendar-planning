from z3 import *

# Define participants' busy times in minutes since 9:00 for each day
diane = {
    0: [(180, 210), (360, 390)],       # Monday
    1: [(60, 120), (150, 180), (210, 240), (420, 480)],  # Tuesday
    2: [(0, 30), (330, 360), (450, 480)],  # Wednesday
    3: [(390, 450)],                   # Thursday
    4: [(30, 150), (330, 360), (420, 480)]  # Friday
}

matthew = {
    0: [(0, 60), (90, 480)],           # Monday
    1: [(0, 480)],                     # Tuesday
    2: [(0, 120), (180, 270), (420, 480)],  # Wednesday
    3: [(0, 420)],                     # Thursday
    4: [(0, 480)]                      # Friday
}

# Create variables
day = Int('day')
start_time = Int('start_time')

# Initialize optimizer
opt = Optimize()

# Day constraints (0=Monday, 4=Friday)
opt.add(day >= 0, day <= 4)

# Meeting duration: 1 hour (60 minutes), must end by 17:00 (480 minutes)
opt.add(start_time >= 0)
opt.add(start_time + 60 <= 480)

# Add constraints for Diane's availability
for d in range(5):
    for (s, e) in diane[d]:
        opt.add(Implies(day == d, Or(start_time + 60 <= s, start_time >= e)))

# Add constraints for Matthew's availability
for d in range(5):
    for (s, e) in matthew[d]:
        opt.add(Implies(day == d, Or(start_time + 60 <= s, start_time >= e)))

# Matthew prefers not to meet on Wednesday before 12:30 (210 minutes)
opt.add(Implies(day == 2, start_time >= 210))

# Optimize for earliest possible time (day then start time)
opt.minimize(day * 1000 + start_time)

# Solve and output
if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    s = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_str = days[d]
    start_h = 9 + s // 60
    start_m = s % 60
    end_time = s + 60
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    print(f"Day: {day_str}, Start: {start_h:02}:{start_m:02}, End: {end_h:02}:{end_m:02}")
else:
    print("No solution found")