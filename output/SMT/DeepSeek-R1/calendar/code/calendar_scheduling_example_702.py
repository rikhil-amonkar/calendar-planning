from z3 import Optimize, Int, If, Or, And, sat

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 30  # 30 minutes

# Days: Monday(0), Tuesday(1), Wednesday(2)
opt.add(day >= 0, day <= 2)
opt.add(start >= 0, start + duration <= 480)

# Robert's preference: avoid Monday
opt.add(day != 0)

# Robert's busy periods converted to minutes since 9:00
robert_busy = {
    1: [(90, 120), (360, 390)],  # Tuesday: 10:30-11:00, 15:00-15:30
    2: [(60, 120), (150, 180), (210, 240), (270, 300), (360, 390), (420, 450)]  # Wednesday
}

# Ralph's busy periods converted to minutes since 9:00
ralph_busy = {
    1: [(0, 30), (60, 90), (120, 150), (180, 240), (300, 390), (420, 480)],  # Tuesday
    2: [(90, 120), (150, 180), (240, 330), (450, 480)]  # Wednesday
}

# Add constraints for Robert's availability
for d, slots in robert_busy.items():
    opt.add(If(day == d,
        And([Or(start + duration <= s, start >= e) for (s, e) in slots]),
        True))

# Add constraints for Ralph's availability
for d, slots in ralph_busy.items():
    opt.add(If(day == d,
        And([Or(start + duration <= s, start >= e) for (s, e) in slots]),
        True))

# Optimize for earliest day and start time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    days = ["Monday", "Tuesday", "Wednesday"]
    hours = 9 + start_val // 60
    minutes = start_val % 60
    print(f"Meeting starts on {days[day_val]} at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")