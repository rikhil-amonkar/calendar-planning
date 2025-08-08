from z3 import *

def main():
    # Create a solver
    solver = Solver()
    
    # Define the start time variable in minutes
    start_minutes = Int('start_minutes')
    
    # Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
    # Meeting must start at or after 9:00 and end by 17:00
    solver.add(start_minutes >= 540)
    solver.add(start_minutes + 30 <= 1020)
    
    # Evelyn's constraint: meeting must end by 13:00 (780 minutes)
    solver.add(start_minutes + 30 <= 780)
    
    # Randy's blocked intervals (half-open: [start, end))
    # Avoid [540, 630)
    solver.add(Or(start_minutes + 30 <= 540, start_minutes >= 630))
    # Avoid [660, 930)
    solver.add(Or(start_minutes + 30 <= 660, start_minutes >= 930))
    # Avoid [960, 1020)
    solver.add(Or(start_minutes + 30 <= 960, start_minutes >= 1020))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        s = model[start_minutes].as_long()
        
        # Convert start time to HH:MM
        start_hour = s // 60
        start_minute = s % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time
        end_minutes = s + 30
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution in the required format
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()