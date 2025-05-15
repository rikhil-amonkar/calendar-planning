from z3 import *

# Convert blocked times to minutes since 9:00 for each day
martha = {
    0: [(420, 480)],          # Monday 16:00-17:00
    1: [(360, 390)],          # Tuesday 15:00-15:30
    2: [(60, 120), (300, 330)]  # Wednesday
}

beverly = {
    0: [(0, 270), (300, 480)],  # Monday
    1: [(0, 480)],             # Tuesday (full day)
    2: [(30, 390), (450, 480)] # Wednesday
}

# Create variables
day = Int('day')
start_time = Int('start_time')
opt = Optimize()

# Day must be Monday (0), Tuesday (1), or Wednesday (2)
opt.add(Or(day == 0, day == 1, day == 2))

# Meeting duration is 60 minutes (9:00-17:00 = 480 minutes total)
opt.add(start_time >= 0)
opt.add(start_time + 60 <= 480)

# Tuesday is fully blocked for Beverly
opt.add(day != 1)

# Add availability constraints for selected day
def add_availability(participant_schedule):
    for d in participant_schedule:
        # For each busy block on day d, meeting must be before or after
        opt.add(Implies(day == d, And([
            Or(start_time + 60 <= busy_start, start_time >= busy_end)
            for (busy_start, busy_end) in participant_schedule[d]
        ])))

add_availability(martha)
add_availability(beverly)

# Find earliest possible time (prioritize earlier days then earlier times)
opt.minimize(day * 1000 + start_time)

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    s = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday"]
    start_h = 9 + s // 60
    start_m = s % 60
    end_time = s + 60
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    print(f"Day: {days[d]}, Start: {start_h:02}:{start_m:02}, End: {end_h:02}:{end_m:02}")
else:
    print("No solution found")