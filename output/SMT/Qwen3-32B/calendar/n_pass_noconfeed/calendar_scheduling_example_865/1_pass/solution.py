import z3

def to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

megan_busy = {
    'Monday': [(780, 810), (840, 930)],
    'Tuesday': [(540, 570), (720, 750), (960, 1020)],
    'Wednesday': [(570, 600), (630, 690), (750, 840), (960, 990)],
    'Thursday': [(810, 870), (900, 930)]
}

daniel_busy = {
    'Monday': [(600, 690), (750, 900)],
    'Tuesday': [(540, 600), (630, 1020)],
    'Wednesday': [(540, 600), (630, 690), (720, 1020)],
    'Thursday': [(540, 720), (750, 870), (900, 930), (960, 1020)]
}

for day in days:
    s = z3.Int('s')
    solver = z3.Optimize()
    solver.add(s >= 540)
    solver.add(s + 60 <= 1020)

    for b_start, b_end in megan_busy[day]:
        solver.add(z3.Or(s + 60 <= b_start, s >= b_end))
    
    for b_start, b_end in daniel_busy[day]:
        solver.add(z3.Or(s + 60 <= b_start, s >= b_end))
    
    solver.minimize(s)
    
    if solver.check() == z3.sat:
        model = solver.model()
        start_time = model[s].as_long()
        end_time = start_time + 60
        start_str = to_time(start_time)
        end_str = to_time(end_time)
        print(f"{start_str}:{end_str} on {day}")
        break