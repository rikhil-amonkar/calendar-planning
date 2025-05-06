from z3 import Optimize, Int, If, Or, And, sat

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 60  # 1 hour

# Days: Monday(0), Tuesday(1), Wednesday(2), Thursday(3), Friday(4)
opt.add(day >= 0, day <= 4)
opt.add(start >= 0, start + duration <= 480)

# Betty cannot meet on Wednesday(2) and Thursday(3)
opt.add(Or(day == 0, day == 1, day == 4))

# Megan cannot meet on Monday(0) and Friday(4)
opt.add(Or(day == 1, day == 2, day == 3))

# Betty's constraints per day
betty_busy = {
    0: [(60, 90), (150, 210), (420, 450)],   # Monday
    1: [(30, 60), (90, 120), (180, 210), (270, 360), (450, 480)],  # Tuesday
    4: [(0, 60), (150, 180), (210, 240), (330, 360)]  # Friday
}
for d, slots in betty_busy.items():
    opt.add(If(day == d,
        And([Or(start + duration <= s, start >= e) for (s, e) in slots]),
        True))

# Megan's constraints per day
megan_busy = {
    0: [(0, 480)],  # Monday (full day)
    1: [(0, 30), (60, 90), (180, 300), (360, 390), (420, 450)],  # Tuesday
    2: [(30, 90), (120, 150), (210, 240), (270, 330), (390, 480)],  # Wednesday
    3: [(0, 90), (150, 300), (330, 360), (390, 450)],  # Thursday
    4: [(0, 480)]  # Friday (full day)
}
for d, slots in megan_busy.items():
    opt.add(If(day == d,
        And([Or(start + duration <= s, start >= e) for (s, e) in slots]),
        True))

# Find earliest possible day and time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    hours = 9 + start_val // 60
    minutes = start_val % 60
    print(f"Meeting starts on {days[day_val]} at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")