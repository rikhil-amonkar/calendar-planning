from z3 import *

# Define participants' busy times in minutes since 9:00 for each day
laura = {
    0: [(90, 120), (210, 240), (330, 390), (420, 480)],   # Monday
    1: [(30, 60), (120, 150), (240, 270), (330, 360), (420, 480)],  # Tuesday
    3: [(90, 120), (180, 270), (360, 390), (420, 450)]    # Thursday
}

philip = {
    0: [(0, 480)],                                         # Monday (full day)
    1: [(0, 120), (150, 180), (240, 270), (300, 330), (360, 450)],  # Tuesday
    3: [(0, 90), (120, 210), (240, 480)]                   # Thursday
}

# Create variables
day = Int('day')
start_time = Int('start_time')
opt = Optimize()

# Day constraints (0=Monday, 1=Tuesday, 3=Thursday)
opt.add(Or(day == 0, day == 1, day == 3))

# Meeting duration: 1 hour (60 minutes), must end by 17:00 (480 minutes)
opt.add(start_time >= 0)
opt.add(start_time + 60 <= 480)

# Add availability constraints using day-dependent implications
def add_schedule_constraints(schedule, participant):
    for d in schedule:
        for (s, e) in schedule[d]:
            opt.add(Implies(day == d, Or(start_time + 60 <= s, start_time >= e)))

add_schedule_constraints(laura, "Laura")
add_schedule_constraints(philip, "Philip")

# Optimize for earliest possible time (day priority then start time)
opt.minimize(day * 1000 + start_time)

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    s = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_str = days[d]
    start_h = 9 + s // 60
    start_m = s % 60
    end_time = s + 60
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    print(f"Day: {day_str}, Start: {start_h:02}:{start_m:02}, End: {end_h:02}:{end_m:02}")
else:
    print("No solution found")