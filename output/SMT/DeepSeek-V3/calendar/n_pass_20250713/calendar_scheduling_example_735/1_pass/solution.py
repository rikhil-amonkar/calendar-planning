from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()
    
    # Define the possible days (0: Monday, 1: Tuesday, 2: Wednesday)
    day = Int('day')
    s.add(day >= 0, day <= 2)
    
    # Define the start time in minutes from 9:00 (540 minutes since 9*60=540)
    start_time = Int('start_time')  # in minutes from 0:00
    # Working hours 9:00-17:00 (540 to 1020 minutes)
    s.add(start_time >= 540, start_time + 30 <= 1020)
    
    # Blocked times for Ronald and Amber for each day
    # Structure: {day: [(start1, end1), (start2, end2), ...]}
    ronald_blocked = {
        0: [(10*60 + 30, 11*60), (12*60, 12*60 + 30), (15*60 + 30, 16*60)],
        1: [(9*60, 9*60 + 30), (12*60, 12*60 + 30), (15*60 + 30, 16*60 + 30)],
        2: [(9*60 + 30, 10*60 + 30), (11*60, 12*60), (12*60 + 30, 13*60), (13*60 + 30, 14*60), (16*60 + 30, 17*60)]
    }
    
    amber_blocked = {
        0: [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60 + 30, 12*60), (12*60 + 30, 14*60), (14*60 + 30, 15*60), (15*60 + 30, 17*60)],
        1: [(9*60, 9*60 + 30), (10*60, 11*60 + 30), (12*60, 12*60 + 30), (13*60 + 30, 15*60 + 30), (16*60 + 30, 17*60)],
        2: [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 13*60 + 30), (15*60, 15*60 + 30)]
    }
    
    # Constraints for each day
    # For the selected day, the meeting should not overlap with any blocked times of Ronald or Amber
    def no_overlap(day_val, start, end, blocked_times):
        constraints = []
        for (block_start, block_end) in blocked_times:
            constraints.append(Or(
                end <= block_start,
                start >= block_end
            ))
        return And(constraints)
    
    # Constraints based on the selected day
    day_constraints = []
    for d in [0, 1, 2]:
        # If day is d, then apply the constraints for that day
        r_blocked = ronald_blocked[d]
        a_blocked = amber_blocked[d]
        day_constraints.append(And(
            day == d,
            no_overlap(d, start_time, start_time + 30, r_blocked),
            no_overlap(d, start_time, start_time + 30, a_blocked)
        ))
    
    s.add(Or(day_constraints))
    
    # To find the earliest time, we can minimize the start_time
    # But Z3's optimizer can handle this
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(start_time)
    
    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        
        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday"]
        day_name = days[day_val]
        
        # Convert start_val to HH:MM
        hours = start_val // 60
        minutes = start_val % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_val = start_val + 30
        end_hours = end_val // 60
        end_minutes = end_val % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()