import z3

robert_busy = {
    0: [(660, 690), (840, 870), (930, 960)],
    1: [(630, 660), (900, 930)],
    2: [(600, 660), (690, 720), (750, 780), (810, 840), (900, 930), (960, 990)],
}

ralph_busy = {
    0: [(600, 810), (840, 870), (900, 1020)],
    1: [(540, 570), (600, 630), (660, 690), (720, 780), (840, 930), (960, 1020)],
    2: [(630, 660), (690, 720), (780, 870), (990, 1020)],
}

day_names = ['Monday', 'Tuesday', 'Wednesday']

for day in [1, 2, 0]:  # Check Tuesday, Wednesday, Monday
    rob_intervals = robert_busy[day]
    ral_intervals = ralph_busy[day]
    
    opt = z3.Optimize()
    s = z3.Int('s')
    opt.add(s >= 540)
    opt.add(s + 30 <= 1020)
    
    for start, end in rob_intervals:
        opt.add(z3.Or(s >= end, s + 30 <= start))
    
    for start, end in ral_intervals:
        opt.add(z3.Or(s >= end, s + 30 <= start))
    
    opt.minimize(s)
    
    if opt.check() == z3.sat:
        model = opt.model()
        s_val = model[s].as_long()
        day_name = day_names[day]
        
        def mins_to_time(m):
            hours = m // 60
            mins = m % 60
            return f"{hours:02d}:{mins:02d}"
        
        start_time = mins_to_time(s_val)
        end_time = mins_to_time(s_val + 30)
        
        print(f"SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
        break