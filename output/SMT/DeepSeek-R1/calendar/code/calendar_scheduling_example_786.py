from z3 import Optimize, Int, If, Or, And, Not, sat

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 30  # 30 minutes

# Day can be Monday(0), Tuesday(1), Wednesday(2)
opt.add(day >= 0, day <= 2)
opt.add(start >= 0, start + duration <= 480)  # Time must fit within 9:00-17:00

# Pamela's preference: avoid meetings before 16:00 (420 minutes)
opt.add(start >= 420)

# Amy's constraints (only on Wednesday)
amy_overlap_wed = Or(
    And(day == 2, start < 120, start + duration > 120),  # 11:00-11:30 (120-150)
    And(day == 2, start < 270, start + duration > 270)   # 13:30-14:00 (270-300)
)
opt.add(Not(amy_overlap_wed))

# Pamela's per-day busy periods
# Monday: 0-90 (9:00-10:30), 120-450 (11:00-16:30)
opt.add(If(day == 0, start >= 450, True))  # Must start after 16:30 on Monday

# Tuesday: 0-30 (9:00-9:30), 60-480 (10:00-17:00) → No valid time after 16:00
opt.add(If(day == 1, start >= 480, True))  # Impossible constraint to exclude Tuesday

# Wednesday: 0-30 (9:00-9:30), 60-120 (10:00-11:00), 150-270 (11:30-13:30), 
#           330-360 (14:30-15:00), 420-450 (16:00-16:30)
opt.add(If(day == 2, start >= 450, True))  # Must start after 16:30 on Wednesday

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