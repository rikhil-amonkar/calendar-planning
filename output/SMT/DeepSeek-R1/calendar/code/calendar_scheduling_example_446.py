from z3 import Optimize, Int, Or, sat

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes

# Convert time constraints to minutes since 9:00 (0-480)
opt.add(start >= 0, start + duration <= 480)

# Megan's busy periods (minutes since 9:00)
megan_busy = [
    (0, 30),    # 9:00-9:30
    (60, 120),  # 10:00-11:00
    (180, 210)  # 12:00-12:30
]
for (s, e) in megan_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Christine's busy periods
christine_busy = [
    (0, 30),     # 9:00-9:30
    (150, 180),  # 11:30-12:00
    (240, 300),  # 13:00-14:00
    (390, 420)   # 15:30-16:30
]
for (s, e) in christine_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Sara's busy periods
sara_busy = [
    (150, 180),  # 11:30-12:00
    (270, 300)   # 14:30-15:00
]
for (s, e) in sara_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Bruce's busy periods
bruce_busy = [
    (30, 60),    # 9:30-10:00
    (90, 180),   # 10:30-12:00
    (210, 300),  # 12:30-14:00
    (270, 300),  # 14:30-15:00
    (390, 450)   # 15:30-16:30
]
for (s, e) in bruce_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Kathryn's busy periods
kathryn_busy = [
    (60, 390),   # 10:00-15:30
    (420, 450)   # 16:00-16:30
]
for (s, e) in kathryn_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Billy's busy periods
billy_busy = [
    (0, 30),     # 9:00-9:30
    (120, 150),  # 11:00-11:30
    (180, 300),  # 12:00-14:00
    (270, 330)   # 14:30-15:30
]
for (s, e) in billy_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Find earliest possible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    start_min = m[start].as_long()
    hours = 9 + start_min // 60
    minutes = start_min % 60
    print(f"Meeting starts on Monday at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")