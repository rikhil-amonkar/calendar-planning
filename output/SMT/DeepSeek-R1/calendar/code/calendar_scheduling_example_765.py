from z3 import *

# Convert busy times to minutes since 9:00 for each day
joshua = {
    0: [(360, 390)],   # Monday 15:00-15:30
    1: [(150, 180), (240, 270), (330, 360)]  # Tuesday
}

joyce = {
    0: [(0, 30), (60, 120), (150, 180), (240, 360), (390, 480)],  # Monday
    1: [(0, 480)],  # Tuesday (full day)
    2: [(0, 30), (60, 120), (210, 390), (420, 450)]  # Wednesday
}

# Create variables
day = Int('day')
start_time = Int('start_time')
opt = Optimize()

# Day constraints (0=Monday, 1=Tuesday, 2=Wednesday)
opt.add(Or(day == 0, day == 1, day == 2))

# Joyce cannot meet on Tuesday (full day) or Wednesday (preference)
opt.add(day != 1)  # Tuesday excluded
opt.add(day != 2)  # Wednesday preference excluded

# Meeting constraints: 30 minutes within 9:00-17:00 (480 minutes)
opt.add(start_time >= 0)
opt.add(start_time + 30 <= 480)

# Joyce's Monday constraint: Can't meet before 12:00 (180 minutes)
opt.add(Implies(day == 0, start_time >= 180))

# Add availability constraints for selected day
def add_day_constraints(participant_schedule):
    for d in participant_schedule:
        opt.add(Implies(day == d, And([Or(start_time + 30 <= s, start_time >= e) 
                                    for (s, e) in participant_schedule[d]])))

add_day_constraints(joshua)
add_day_constraints(joyce)

# Optimize for earliest possible time
opt.minimize(day * 1000 + start_time)

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    s = m[start_time].as_long()
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[d]
    start_h = 9 + s // 60
    start_m = s % 60
    end_time = s + 30
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    print(f"Day: {day_str}, Start: {start_h:02}:{start_m:02}, End: {end_h:02}:{end_m:02}")
else:
    print("No solution found")