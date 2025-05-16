from z3 import *

opt = Optimize()
day = Int('day')
start = Int('start')
duration = 30  # 30 minutes meeting

# Meeting must be on Monday
opt.add(day == 0)
opt.add(start >= 0)
opt.add(start + duration <= 240)  # Harold's constraint: end by 13:00 (240 minutes)

# Blocked times in minutes since 9:00 (Monday only)
jacqueline_blocks = [(0, 30), (120, 150), (210, 240)]
harold_blocks = [(60, 90)]
arthur_blocks = [(0, 30), (60, 210)]
kelly_blocks = [(0, 30), (60, 120), (150, 210)]

# Add constraints for each person's blocked intervals
for s, e in jacqueline_blocks:
    opt.add(Or(start >= e, start + duration <= s))
for s, e in harold_blocks:
    opt.add(Or(start >= e, start + duration <= s))
for s, e in arthur_blocks:
    opt.add(Or(start >= e, start + duration <= s))
for s, e in kelly_blocks:
    opt.add(Or(start >= e, start + duration <= s))

# Optimize for earliest possible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    st = m[start].as_long()
    days = ['Monday']
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + duration) // 60
    end_m = (st + duration) % 60
    print(f"{days[0]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No valid slot found")