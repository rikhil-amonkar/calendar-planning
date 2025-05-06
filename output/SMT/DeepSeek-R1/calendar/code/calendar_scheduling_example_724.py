from z3 import Optimize, Int, If, Or, And, sat

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 30  # 30 minutes

# Day can be Monday(0), Tuesday(1), Wednesday(2)
opt.add(day >= 0, day <= 2)
opt.add(start >= 0, start + duration <= 480)  # Time must fit within 9:00-17:00

# Tyler's constraints
# Monday: prefers after 16:00 (420 minutes)
opt.add(If(day == 0, start >= 420, True))

# Tyler's busy periods for Tuesday
opt.add(If(day == 1,
    And(
        Or(start + duration <= 0, start >= 30),    # 9:00-9:30
        Or(start + duration <= 330, start >= 360)  # 14:30-15:00
    ),
    True
))

# Tyler's busy periods for Wednesday
opt.add(If(day == 2,
    And(
        Or(start + duration <= 90, start >= 120),  # 10:30-11:00
        Or(start + duration <= 210, start >= 240), # 12:30-13:00
        Or(start + duration <= 270, start >= 300), # 13:30-14:00
        Or(start + duration <= 450, start >= 480)  # 16:30-17:00
    ),
    True
))

# Ruth's constraints
# Monday busy periods
opt.add(If(day == 0,
    And(
        Or(start + duration <= 0, start >= 60),    # 9:00-10:00
        Or(start + duration <= 90, start >= 180),   # 10:30-12:00
        Or(start + duration <= 210, start >= 330),  # 12:30-14:30
        Or(start + duration <= 360, start >= 420),  # 15:00-16:00
        Or(start + duration <= 450, start >= 480)   # 16:30-17:00
    ),
    True
))

# Ruth is busy all day on Tuesday and Wednesday
opt.add(If(day == 1, start >= 480, True))  # Impossible constraint
opt.add(If(day == 2, start >= 480, True))  # Impossible constraint

# Find earliest day and time
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