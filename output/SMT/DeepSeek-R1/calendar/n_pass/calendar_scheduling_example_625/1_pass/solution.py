from z3 import *

def main():
    s = Int('s')
    d = Int('d')
    
    constraints = [
        s >= 0,
        s <= 450,
        Or(d == 0, d == 1)
    ]
    
    monday_busy = [(0, 60), (90, 480)]
    tuesday_busy = [(0, 30), (90, 150), (210, 270), (330, 390), (420, 480)]
    
    monday_avoid = []
    for (b_start, b_end) in monday_busy:
        monday_avoid.append(Or(s + 30 <= b_start, s >= b_end))
        
    tuesday_avoid = []
    for (b_start, b_end) in tuesday_busy:
        tuesday_avoid.append(Or(s + 30 <= b_start, s >= b_end))
        
    constraints.append(If(d == 0, And(monday_avoid), If(d == 1, And(tuesday_avoid), True)))
    
    solver = Solver()
    solver.add(constraints)
    
    solver.push()
    solver.add(d == 1, s >= 330)
    if solver.check() == sat:
        model = solver.model()
        d_val = model[d].as_long()
        s_val = model[s].as_long()
        solver.pop()
    else:
        solver.pop()
        solver.push()
        solver.add(d == 1)
        if solver.check() == sat:
            model = solver.model()
            d_val = model[d].as_long()
            s_val = model[s].as_long()
            solver.pop()
        else:
            solver.pop()
            solver.push()
            solver.add(d == 0)
            if solver.check() == sat:
                model = solver.model()
                d_val = model[d].as_long()
                s_val = model[s].as_long()
                solver.pop()
            else:
                solver.pop()
                solver.check()
                model = solver.model()
                d_val = model[d].as_long()
                s_val = model[s].as_long()
    
    total_minutes = s_val
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_hour = 9 + hours
    start_time = f"{start_hour:02d}:{minutes:02d}"
    
    total_minutes_end = s_val + 30
    hours_end = total_minutes_end // 60
    minutes_end = total_minutes_end % 60
    end_hour = 9 + hours_end
    end_time = f"{end_hour:02d}:{minutes_end:02d}"
    
    day_str = "Monday" if d_val == 0 else "Tuesday"
    
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == '__main__':
    main()