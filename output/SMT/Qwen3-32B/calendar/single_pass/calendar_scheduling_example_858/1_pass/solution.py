from z3 import *

def schedule_meeting():
    solver = Optimize()
    
    day = Int('day')
    start = Int('start')
    
    # Constraints on day and start time
    solver.add(0 <= day, day <= 3)
    solver.add(540 <= start, start <= 960)  # 9:00 to 16:00 (since meeting is 1h)
    
    # Define busy intervals for Carl and Margaret
    carl_busy = [
        # Monday
        [(11 * 60 + 0, 11 * 60 + 30)],  # 11:00-11:30
        # Tuesday
        [(14 * 60 + 30, 15 * 60 + 0)],  # 14:30-15:00
        # Wednesday
        [(10 * 60, 11 * 60 + 30), (13 * 60, 13 * 60 + 30)],  # 10:00-11:30, 13:00-13:30
        # Thursday
        [(13 * 60 + 30, 14 * 60), (16 * 60, 16 * 60 + 30)]  # 13:30-14:00, 16:00-16:30
    ]
    
    margaret_busy = [
        # Monday
        [(9 * 60, 10 * 60 + 30), (11 * 60, 17 * 60)],  # 9:00-10:30, 11:00-17:00
        # Tuesday
        [(9 * 60 + 30, 12 * 60), (13 * 60 + 30, 14 * 60), (15 * 60 + 30, 17 * 60)],  # 9:30-12:00, 13:30-14:00, 15:30-17:00
        # Wednesday
        [(9 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60 + 30), (15 * 60, 17 * 60)],  # 9:30-12:00, 12:30-13:00, 13:30-14:30, 15:00-17:00
        # Thursday
        [(10 * 60, 12 * 60), (12 * 60 + 30, 14 * 60), (14 * 60 + 30, 17 * 60)]  # 10:00-12:00, 12:30-14:00, 14:30-17:00
    ]
    
    # Add Carl's constraints
    carl_constraints = []
    for d in range(4):
        constraints = []
        for (b_start, b_end) in carl_busy[d]:
            constraints.append(Or(start + 60 <= b_start, start >= b_end))
        day_constraint = And(constraints)
        carl_constraints.append(Implies(day == d, day_constraint))
    solver.add(And(carl_constraints))
    
    # Add Margaret's constraints
    margaret_constraints = []
    for d in range(4):
        constraints = []
        for (b_start, b_end) in margaret_busy[d]:
            constraints.append(Or(start + 60 <= b_start, start >= b_end))
        day_constraint = And(constraints)
        margaret_constraints.append(Implies(day == d, day_constraint))
    solver.add(And(margaret_constraints))
    
    # Minimize day to prefer earlier days (avoid Thursday)
    solver.minimize(day)
    
    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_val = model[start].as_long()
        end_val = start_val + 60
        
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_name = days[day_val]
        
        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {to_time_str(start_val)}")
        print(f"End Time: {to_time_str(end_val)}")
    else:
        print("No solution found.")

schedule_meeting()