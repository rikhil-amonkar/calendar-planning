from z3 import *

def main():
    s = Int('s')
    
    constraints = [
        s >= 0,
        s <= 450   # because 450 + 30 = 480 minutes (17:00)
    ]
    
    raymond_intervals = [
        (0, 30),    # 9:00-9:30
        (150, 180), # 11:30-12:00
        (240, 270), # 13:00-13:30
        (360, 390)  # 15:00-15:30
    ]
    
    billy_intervals = [
        (60, 90),   # 10:00-10:30
        (180, 240), # 12:00-13:00
        (450, 480)  # 16:30-17:00
    ]
    
    donald_intervals = [
        (0, 30),    # 9:00-9:30
        (60, 120),  # 10:00-11:00
        (180, 240), # 12:00-13:00
        (300, 330), # 14:00-14:30
        (420, 480)  # 16:00-17:00
    ]
    
    def add_interval_constraints(intervals):
        cons = []
        for (a, b) in intervals:
            cons.append(Or(s + 30 <= a, s >= b))
        return cons
    
    constraints += add_interval_constraints(raymond_intervals)
    constraints += add_interval_constraints(billy_intervals)
    constraints += add_interval_constraints(donald_intervals)
    
    solver = Solver()
    solver.add(constraints)
    
    pref_constraint = (s + 30 <= 360)  # End by 15:00 (360 minutes from 9:00)
    
    solver.push()
    solver.add(pref_constraint)
    if solver.check() == sat:
        model = solver.model()
    else:
        solver.pop()
        if solver.check() == sat:
            model = solver.model()
        else:
            print("No solution found")
            return
    
    s_val = model.eval(s).as_long()
    
    total_minutes = 9 * 60 + s_val
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{hours:02d}:{minutes:02d}"
    
    end_minutes = total_minutes + 30
    end_hours = end_minutes // 60
    end_minutes = end_minutes % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"
    
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == '__main__':
    main()