from z3 import Optimize, Int, Or, And, sat

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 60  # 1 hour

# Day must be Monday (0)
opt.add(day == 0)
opt.add(start >= 0)
opt.add(start + duration <= 480)  # Within 9:00-17:00

# Denise's constraint: meeting must end by 12:30 (210 minutes)
opt.add(start + duration <= 210)

# Ryan's busy periods (Monday)
ryan_busy = [(0, 30), (210, 240)]
for s, e in ryan_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Denise's busy periods (Monday)
denise_busy = [(30, 90), (180, 240), (330, 450)]
for s, e in denise_busy:
    opt.add(Or(start + duration <= s, start >= e))

# Optimize for earliest start time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    start_val = m[start].as_long()
    hours = 9 + start_val // 60
    minutes = start_val % 60
    print(f"Meeting starts on Monday at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found")