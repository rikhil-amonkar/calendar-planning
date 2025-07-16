from z3 import *

def solve_scheduling():
    # Create solver
    s = Solver()
    
    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 9:00 (540)
    duration = 30  # meeting duration in minutes
    
    # Constraints for day: 0 (Monday), 1 (Tuesday), 2 (Wednesday)
    s.add(day >= 0, day <= 2)
    # Arthur cannot meet on Tuesday (day 1)
    s.add(day != 1)
    
    # Work hours: 9:00 (540) to 17:00 (1020)
    s.add(start_time >= 540, start_time + duration <= 1020)
    
    # Arthur's busy times (converted to minutes from 0:00)
    arthur_busy = [
        # Monday
        [(11*60, 11*60 + 30), (13*60 + 30, 14*60), (15*60, 15*60 + 30)],
        # Tuesday (excluded)
        [],
        # Wednesday
        [(10*60, 10*60 + 30), (11*60, 11*60 + 30), (12*60, 12*60 + 30), (14*60, 14*60 + 30), (16*60, 16*60 + 30)]
    ]
    
    # Michael's busy times (converted to minutes from 0:00)
    michael_busy = [
        # Monday
        [(9*60, 12*60), (12*60 + 30, 13*60), (14*60, 14*60 + 30), (15*60, 17*60)],
        # Tuesday
        [(9*60 + 30, 11*60 + 30), (12*60, 13*60 + 30), (14*60, 15*60 + 30)],
        # Wednesday
        [(10*60, 12*60 + 30), (13*60, 13*60 + 30)]
    ]
    
    # Function to check if the meeting overlaps with any busy times for a given day
    def no_overlap(day_val, start, busy_slots):
        for (busy_start, busy_end) in busy_slots:
            s.add(Not(And(start < busy_end, start + duration > busy_start)))
    
    # Add constraints for each possible day
    # Monday (day 0)
    monday_constraint = And(day == 0)
    s.add(Implies(monday_constraint, And(
        no_overlap(0, start_time, arthur_busy[0]),
        no_overlap(0, start_time, michael_busy[0])
    ))
    
    # Wednesday (day 2)
    wednesday_constraint = And(day == 2)
    s.add(Implies(wednesday_constraint, And(
        no_overlap(2, start_time, arthur_busy[2]),
        no_overlap(2, start_time, michael_busy[2])
    ))
    
    # Optimize for earliest start time
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(start_time)
    
    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        
        # Convert day to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        
        # Convert start time to HH:MM
        start_hh = start_val // 60
        start_mm = start_val % 60
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        
        # Calculate end time
        end_val = start_val + duration
        end_hh = end_val // 60
        end_mm = end_val % 60
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"
        
        # Print solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()