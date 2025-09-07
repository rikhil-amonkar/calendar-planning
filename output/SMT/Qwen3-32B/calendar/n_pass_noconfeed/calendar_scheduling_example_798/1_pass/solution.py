from z3 import *

opt = Optimize()

day = Int('day')
start = Int('start')

opt.add(Or(day == 0, day == 1, day == 2))
opt.add(And(start >= 540, start <= 990))  # 9:00 to 16:30

nancy_busy = {
    0: [(600, 630), (690, 750), (810, 840), (870, 930), (960, 1020)],
    1: [(570, 630), (660, 690), (720, 750), (780, 810), (930, 960)],
    2: [(600, 690), (810, 960)]
}

jose_busy = {
    0: [(540, 1020)],
    1: [(540, 1020)],
    2: [(540, 570), (600, 750), (810, 870), (900, 1020)]
}

for d in range(3):
    for b_start, b_end in nancy_busy[d]:
        opt.add(If(day == d, Or(start + 30 <= b_start, start >= b_end), True))
    for b_start, b_end in jose_busy[d]:
        opt.add(If(day == d, Or(start + 30 <= b_start, start >= b_end), True))

opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday']
    day_name = days[day_val]
    start_h = start_val // 60
    start_m = start_val % 60
    end_val = start_val + 30
    end_h = end_val // 60
    end_m = end_val % 60
    time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    print(f"{day_name} {time_str}")
else:
    print("No solution")