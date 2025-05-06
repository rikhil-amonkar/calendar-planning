from z3 import Optimize, Int, Or, sat

opt = Optimize()
start = Int('start')
duration = 30  # 30 minutes

# Convert time constraints to minutes since 9:00 (0-480)
opt.add(start >= 0, start + duration <= 480)

# Gregory's busy periods (minutes since 9:00)
gregory_busy = [
    (0, 60),    # 9:00-10:00
    (90, 150),  # 10:30-11:30
    (210, 240), # 12:30-13:00
    (270, 300)  # 13:30-14:00
]
for (s, e) in gregory_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Christine's busy periods
christine_busy = [
    (0, 150),   # 9:00-11:30
    (270, 480)  # 13:30-17:00
]
for (s, e) in christine_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Vincent's busy periods
vincent_busy = [
    (0, 30),    # 9:00-9:30
    (90, 180),  # 10:30-12:00
    (210, 300), # 12:30-14:00
    (330, 480)  # 14:30-17:00
]
for (s, e) in vincent_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Natalie has no constraints

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