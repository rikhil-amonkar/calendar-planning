from z3 import Optimize, Int, If, Or, And, sat

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 30  # 30 minutes

# Day can be Monday(0), Tuesday(1), Wednesday(2), Thursday(3)
opt.add(day >= 0, day <= 3)
opt.add(start >= 0, start + duration <= 480)  # 9:00-17:00 in minutes

# Julie's preference: avoid Thursday before 11:30 (150 minutes)
opt.add(If(day == 3, start >= 150, True))

# Ruth's constraints
# Monday-Wednesday: completely busy
for d in [0, 1, 2]:
    opt.add(If(day == d, start >= 480, True))  # Force impossible times

# Thursday constraints for Ruth
thurs_busy = [
    (0, 120),    # 9:00-11:00
    (150, 330),  # 11:30-14:30
    (360, 480)   # 15:00-17:00
]
opt.add(If(day == 3, 
    And([Or(start + duration <= s, start >= e) for (s, e) in thurs_busy]),
    True))

# Find earliest possible day and time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    hours = 9 + start_val // 60
    minutes = start_val % 60
    print(f"Meeting starts on {days[day_val]} at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")