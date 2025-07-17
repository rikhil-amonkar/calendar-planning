from z3 import *

def main():
    # Initialize solver
    solver = Solver()
    
    # Define variables
    d = Int('d')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from midnight
    
    # Constraints for day and time boundaries
    solver.add(Or(d == 0, d == 1, d == 2))
    solver.add(start_time >= 540)  # 9:00
    solver.add(start_time <= 990)  # 16:30 (so that meeting ends by 17:00)
    
    # Jennifer's busy intervals in minutes from midnight
    # Monday: [540,660], [690,780], [810,870], [900,1020]
    monday_constraints = And(
        Or(start_time + 30 <= 540, start_time >= 660),
        Or(start_time + 30 <= 690, start_time >= 780),
        Or(start_time + 30 <= 810, start_time >= 870),
        Or(start_time + 30 <= 900, start_time >= 1020),
        start_time + 30 <= 870  # John's preference: end by 14:30 (870 minutes)
    )
    
    # Tuesday: [540,690], [720,1020]
    tuesday_constraints = And(
        Or(start_time + 30 <= 540, start_time >= 690),
        Or(start_time + 30 <= 720, start_time >= 1020)
    )
    
    # Wednesday: [540,690], [720,750], [780,840], [870,960], [990,1020]
    wednesday_constraints = And(
        Or(start_time + 30 <= 540, start_time >= 690),
        Or(start_time + 30 <= 720, start_time >= 750),
        Or(start_time + 30 <= 780, start_time >= 840),
        Or(start_time + 30 <= 870, start_time >= 960),
        Or(start_time + 30 <= 990, start_time >= 1020)
    )
    
    # Apply day-specific constraints
    solver.add(If(d == 0, monday_constraints, 
                  If(d == 1, tuesday_constraints, 
                     wednesday_constraints)))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        day_val = model[d].as_long()
        start_minutes = model[start_time].as_long()
        
        # Convert day value to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        
        # Convert start time to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + 30
        end_hours = end_minutes // 60
        end_minutes %= 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()