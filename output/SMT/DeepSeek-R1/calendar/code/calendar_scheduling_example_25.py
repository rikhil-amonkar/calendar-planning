from z3 import Optimize, Int, Or, sat

opt = Optimize()
start = Int('start')
duration = 60  # 1 hour

# Convert time constraints to minutes since 9:00 (0-480)
opt.add(start >= 0, start + duration <= 480)  # Must fit within 9:00-17:00

# Pamela's constraint: meeting must end by 14:30 (330 minutes from 9:00)
opt.add(start + duration <= 330)

# Anthony's busy periods (minutes since 9:00)
anthony_busy = [
    (30, 60),    # 9:30-10:00
    (180, 240),  # 12:00-13:00
    (420, 450)   # 16:00-16:30 (irrelevant due to Pamela's constraint)
]
for (s, e) in anthony_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Pamela's busy periods
pamela_busy = [
    (30, 60),    # 9:30-10:00
    (450, 480)   # 16:30-17:00 (irrelevant)
]
for (s, e) in pamela_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Zachary's busy periods
zachary_busy = [
    (0, 150),    # 9:00-11:30
    (180, 210),  # 12:00-12:30
    (240, 270),  # 13:00-13:30
    (330, 360),  # 14:30-15:00 (irrelevant)
    (420, 480)   # 16:00-17:00 (irrelevant)
]
for (s, e) in zachary_busy:
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