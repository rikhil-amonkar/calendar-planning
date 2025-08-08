from z3 import *

def main():
    # Create an integer variable for the start time in minutes
    s = Int('s')
    
    # Constraints list
    constraints = []
    
    # Work hours: 9:00 (540) to 17:00 (1020). Meeting duration 30 minutes => s must be between 540 and 990 inclusive.
    constraints.append(s >= 540)
    constraints.append(s <= 990)
    
    # David's preference: not before 14:00 (840 minutes)
    constraints.append(s >= 840)
    
    # Busy intervals in minutes (start, end) for each participant (except Natalie, who is free)
    busy_intervals = [
        # David's busy intervals
        (690, 720), (870, 900),
        # Douglas' busy intervals
        (570, 600), (690, 720), (780, 810), (870, 900),
        # Ralph's busy intervals
        (540, 570), (600, 660), (690, 750), (810, 900), (930, 960), (990, 1020),
        # Jordan's busy intervals
        (540, 600), (720, 750), (780, 810), (870, 900), (930, 1020)
    ]
    
    # For each busy interval, add constraint: meeting does not overlap
    for (busy_start, busy_end) in busy_intervals:
        constraints.append(Or(s + 30 <= busy_start, s >= busy_end))
    
    # Solve the constraints
    solver = Solver()
    for c in constraints:
        solver.add(c)
    
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[s].as_long()
        
        # Convert start_minutes to HH:MM
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start_minutes + 30)
        end_minutes = start_minutes + 30
        end_hours = end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes_remainder:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()