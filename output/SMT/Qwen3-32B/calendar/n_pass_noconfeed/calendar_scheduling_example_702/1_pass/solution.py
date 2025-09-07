import z3

def to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

robert_busy = {
    'Monday': [(11*60, 11*60 + 30), (14*60, 14*60 + 30), (15*60 + 30, 16*60)],
    'Tuesday': [(10*60 + 30, 11*60), (15*60, 15*60 + 30)],
    'Wednesday': [(10*60, 11*60), (11*60 + 30, 12*60), (12*60 + 30, 13*60), (13*60 + 30, 14*60), (15*60, 15*60 + 30), (16*60, 16*60 + 30)]
}

ralph_busy = {
    'Monday': [(10*60, 13*60 + 30), (14*60, 14*60 + 30), (15*60, 17*60)],
    'Tuesday': [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 11*60 + 30), (12*60, 13*60), (14*60, 15*60 + 30), (16*60, 17*60)],
    'Wednesday': [(10*60 + 30, 11*60), (11*60 + 30, 12*60), (13*60, 14*60 + 30), (16*60 + 30, 17*60)]
}

days_order = ['Tuesday', 'Wednesday', 'Monday']

for day in days_order:
    opt = z3.Optimize()
    start = z3.Int('start')
    opt.add(start >= 9*60)  # 9:00 AM
    opt.add(start <= 17*60 - 30)  # 5:00 PM minus 30 minutes

    # Add Robert's constraints
    for busy_s, busy_e in robert_busy[day]:
        opt.add(z3.Or(start + 30 <= busy_s, start >= busy_e))
    
    # Add Ralph's constraints
    for busy_s, busy_e in ralph_busy[day]:
        opt.add(z3.Or(start + 30 <= busy_s, start >= busy_e))
    
    opt.minimize(start)
    
    if opt.check() == z3.sat:
        model = opt.model()
        earliest_start = model[start].as_long()
        start_time = earliest_start
        end_time = start_time + 30
        start_str = to_time(start_time)
        end_str = to_time(end_time)
        print(f"{day} {start_str}:{end_str}")
        exit()