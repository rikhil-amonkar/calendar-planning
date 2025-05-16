from z3 import *

# Convert blocked times to minutes since 9:00 for each day
gary = {
    0: [(30, 60), (120, 240), (300, 330), (450, 480)],  # Monday
    1: [(0, 30), (90, 120), (330, 420)]                 # Tuesday
}

david = {
    0: [(0, 30), (60, 240), (330, 450)],                # Monday
    1: [(0, 30), (60, 90), (120, 210), (240, 330), (360, 420), (450, 480)]  # Tuesday
}

# Create variables
day = Int('day')
start_time = Int('start_time')
opt = Optimize()

# Day must be Monday (0) or Tuesday (1)
opt.add(Or(day == 0, day == 1))

# Meeting duration is 60 minutes (9:00-17:00 = 480 minutes total)
opt.add(start_time >= 0)
opt.add(start_time + 60 <= 480)

# Add availability constraints for selected day
def add_availability(participant_schedule):
    for d in participant_schedule:
        # For each busy block on day d, meeting must be before or after
        opt.add(Implies(day == d, And([
            Or(start_time + 60 <= busy_start, start_time >= busy_end)
            for (busy_start, busy_end) in participant_schedule[d]
        ])))

add_availability(gary)
add_availability(david)

# Find earliest possible time (prioritize earlier days then earlier times)
opt.minimize(day * 1000 + start_time)

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    s = m[start_time].as_long()
    days = ["Monday", "Tuesday"]
    start_h = 9 + s // 60
    start_m = s % 60
    end_time = s + 60
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    print(f"Day: {days[d]}, Start: {start_h:02}:{start_m:02}, End: {end_h:02}:{end_m:02}")
else:
    print("No solution found")