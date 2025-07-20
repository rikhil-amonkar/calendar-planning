from z3 import *

def main():
    d = Int('d')
    s = Int('s')
    
    # Define the busy intervals for Samuel in minutes (from start of day, [start, end))
    Monday_busy = [(630, 660), (720, 750), (780, 900), (930, 990)]
    Tuesday_busy = [(540, 720), (840, 930), (990, 1020)]
    Wednesday_busy = [(630, 660), (690, 720), (750, 780), (840, 870), (900, 960)]
    
    solver = Solver()
    solver.add(d >= 0, d <= 2)
    solver.add(s >= 540, s <= 990)
    
    # Monday constraint: if d==0, then avoid Monday_busy
    monday_constraint = True
    for (busy_start, busy_end) in Monday_busy:
        monday_constraint = And(monday_constraint, Or(s + 30 <= busy_start, s >= busy_end))
    solver.add(If(d == 0, monday_constraint, True))
    
    # Tuesday constraint: if d==1, then avoid Tuesday_busy
    tuesday_constraint = True
    for (busy_start, busy_end) in Tuesday_busy:
        tuesday_constraint = And(tuesday_constraint, Or(s + 30 <= busy_start, s >= busy_end))
    solver.add(If(d == 1, tuesday_constraint, True))
    
    # Wednesday constraint: if d==2, then avoid Wednesday_busy
    wednesday_constraint = True
    for (busy_start, busy_end) in Wednesday_busy:
        wednesday_constraint = And(wednesday_constraint, Or(s + 30 <= busy_start, s >= busy_end))
    solver.add(If(d == 2, wednesday_constraint, True))
    
    opt = Optimize()
    opt.add(solver.assertions())
    objective = d * 1440 + s
    opt.minimize(objective)
    
    if opt.check() == sat:
        m = opt.model()
        day_val = m[d].as_long()
        s_val = m[s].as_long()
        
        day_str = ["Monday", "Tuesday", "Wednesday"][day_val]
        start_hour = s_val // 60
        start_minute = s_val % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        end_minutes = s_val + 30
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()