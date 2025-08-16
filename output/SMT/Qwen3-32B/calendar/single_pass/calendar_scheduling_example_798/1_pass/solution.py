from z3 import *

def solve_scheduling():
    days = ['Monday', 'Tuesday', 'Wednesday']
    nancy_busy = {
        'Monday': [(600, 630), (690, 750), (810, 840), (870, 930), (960, 1020)],
        'Tuesday': [(570, 630), (660, 690), (720, 750), (780, 810), (930, 960)],
        'Wednesday': [(600, 690), (810, 960)]
    }
    jose_busy = {
        'Monday': [(540, 1020)],
        'Tuesday': [(540, 1020)],
        'Wednesday': [(540, 570), (600, 750), (810, 870), (900, 1020)]
    }
    
    best_day = None
    best_start = None
    best_end = None
    day_order = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2}
    
    for day in days:
        opt = Optimize()
        start = Int('start')
        opt.add(start >= 540)
        opt.add(start <= 990)
        
        for bstart, bend in nancy_busy[day]:
            opt.add(Or(start + 30 <= bstart, start >= bend))
        
        for bstart, bend in jose_busy[day]:
            opt.add(Or(start + 30 <= bstart, start >= bend))
        
        opt.minimize(start)
        
        if opt.check() == sat:
            model = opt.model()
            current_start = model[start].as_long()
            current_end = current_start + 30
            
            if best_start is None:
                best_day = day
                best_start = current_start
                best_end = current_end
            else:
                current_day_order = day_order[day]
                best_day_order = day_order[best_day]
                if current_day_order < best_day_order:
                    best_day = day
                    best_start = current_start
                    best_end = current_end
                elif current_day_order == best_day_order:
                    if current_start < best_start:
                        best_start = current_start
                        best_end = current_end
    
    def to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    solution = f"SOLUTION:\nDay: {best_day}\nStart Time: {to_time(best_start)}\nEnd Time: {to_time(best_end)}"
    return solution

print(solve_scheduling())