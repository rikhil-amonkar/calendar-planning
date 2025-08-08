from z3 import *

def main():
    # Days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Convert busy times to minutes (start, end)
    carl_busy = [
        [(11*60, 11*60 + 30)],  # Monday: 11:00-11:30
        [(14*60 + 30, 15*60)],   # Tuesday: 14:30-15:00
        [(10*60, 11*60 + 30), (13*60, 13*60 + 30)],  # Wednesday: 10:00-11:30, 13:00-13:30
        [(13*60 + 30, 14*60), (16*60, 16*60 + 30)]   # Thursday: 13:30-14:00, 16:00-16:30
    ]
    
    margaret_busy = [
        [(9*60, 10*60 + 30), (11*60, 17*60)],  # Monday: 9:00-10:30, 11:00-17:00
        [(9*60 + 30, 12*60), (13*60 + 30, 14*60), (15*60 + 30, 17*60)],  # Tuesday: 9:30-12:00, 13:30-14:00, 15:30-17:00
        [(9*60 + 30, 12*60), (12*60 + 30, 13*60), (13*60 + 30, 14*60 + 30), (15*60, 17*60)],  # Wednesday: 9:30-12:00, 12:30-13:00, 13:30-14:30, 15:00-17:00
        [(10*60, 12*60), (12*60 + 30, 14*60), (14*60 + 30, 17*60)]  # Thursday: 10:00-12:00, 12:30-14:00, 14:30-17:00
    ]
    
    s = Int('s')
    day = Int('day')
    
    solver = Solver()
    solver.add(day >= 0, day <= 2)  # Exclude Thursday initially
    solver.add(s >= 540, s <= 960)   # Meeting must start between 9:00 and 16:00
    
    for d in range(3):  # Days 0,1,2 (Mon, Tue, Wed)
        carl_cons = []
        for interval in carl_busy[d]:
            carl_cons.append(Or(s + 60 <= interval[0], s >= interval[1]))
        margaret_cons = []
        for interval in margaret_busy[d]:
            margaret_cons.append(Or(s + 60 <= interval[0], s >= interval[1]))
        solver.add(Implies(day == d, And(And(carl_cons), And(margaret_cons))))
    
    if solver.check() == sat:
        model = solver.model()
        d_val = model[day].as_long()
        s_val = model[s].as_long()
        day_str = days[d_val]
        start_hour = s_val // 60
        start_minute = s_val % 60
        end_val = s_val + 60
        end_hour = end_val // 60
        end_minute = end_val % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
    else:
        solver2 = Solver()
        solver2.add(day >= 0, day <= 3)  # Include Thursday
        solver2.add(s >= 540, s <= 960)
        for d in range(4):  # Days 0,1,2,3
            carl_cons = []
            for interval in carl_busy[d]:
                carl_cons.append(Or(s + 60 <= interval[0], s >= interval[1]))
            margaret_cons = []
            for interval in margaret_busy[d]:
                margaret_cons.append(Or(s + 60 <= interval[0], s >= interval[1]))
            solver2.add(Implies(day == d, And(And(carl_cons), And(margaret_cons))))
        
        if solver2.check() == sat:
            model = solver2.model()
            d_val = model[day].as_long()
            s_val = model[s].as_long()
            day_str = days[d_val]
            start_hour = s_val // 60
            start_minute = s_val % 60
            end_val = s_val + 60
            end_hour = end_val // 60
            end_minute = end_val % 60
            start_time = f"{start_hour:02d}:{start_minute:02d}"
            end_time = f"{end_hour:02d}:{end_minute:02d}"
        else:
            day_str = "No solution found"
            start_time = ""
            end_time = ""
    
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()