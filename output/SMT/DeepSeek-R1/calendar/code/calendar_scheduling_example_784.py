from z3 import *

# Define participants' busy times in minutes since 9:00 for each day
judith = {
    0: [(180, 210)],  # Monday: 12:00-12:30
    2: [(150, 180)]   # Wednesday: 11:30-12:00
}

timothy = {
    0: [(30, 60), (90, 150), (210, 300), (390, 480)],  # Monday
    1: [(30, 240), (270, 300), (330, 480)],             # Tuesday
    2: [(0, 30), (90, 120), (270, 330), (360, 390), (420, 450)]  # Wednesday
}

# Create variables
day = Int('day')
start_time = Int('start_time')

# Initialize optimizer
opt = Optimize()

# Day constraints (0=Monday, 1=Tuesday, 2=Wednesday)
opt.add(day >= 0, day <= 2)

# Meeting duration: 1 hour (60 minutes), must end by 17:00 (480 minutes)
opt.add(start_time >= 0)
opt.add(start_time + 60 <= 480)

# Judith's availability constraints
for d in judith:
    for (s, e) in judith[d]:
        opt.add(Implies(day == d, Or(start_time + 60 <= s, start_time >= e)))

# Timothy's availability constraints
for d in timothy:
    for (s, e) in timothy[d]:
        opt.add(Implies(day == d, Or(start_time + 60 <= s, start_time >= e)))

# Judith's preferences: avoid Monday and Wednesday before 12:00 (180 minutes)
opt.add(day != 0)  # No meetings on Monday
opt.add(Implies(day == 2, start_time >= 180))  # Wednesday after 12:00

# Optimize for earliest day and start time
opt.minimize(day * 1000 + start_time)

# Solve and output
if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    s = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[d]
    start_h = 9 + s // 60
    start_m = s % 60
    end_time = s + 60
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    print(f"Day: {day_str}, Start: {start_h:02}:{start_m:02}, End: {end_h:02}:{end_m:02}")
else:
    print("No solution found")