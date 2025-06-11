from z3 import *

def main():
    # Start time in minutes from 9:00
    s = Int('s')
    
    # Constraints: within work hours (9:00 to 17:00) and Helen's constraint (end by 15:00)
    constraints = [
        s >= 0,
        s + 30 <= 480,  # End by 17:00
        s + 30 <= 360   # End by 15:00
    ]
    
    # Christine's busy intervals (start, end) in minutes
    christine_busy = [
        (120, 150),  # 11:00 to 11:30
        (360, 390)   # 15:00 to 15:30
    ]
    
    # Helen's busy intervals (start, end) in minutes
    helen_busy = [
        (30, 90),    # 9:30 to 10:30
        (120, 150),  # 11:00 to 11:30
        (180, 210),  # 12:00 to 12:30
        (270, 420),  # 13:30 to 16:00
        (450, 480)   # 16:30 to 17:00
    ]
    
    # Add constraints for Christine's busy intervals
    for (start, end) in christine_busy:
        constraints.append(Or(s + 30 <= start, s >= end))
    
    # Add constraints for Helen's busy intervals
    for (start, end) in helen_busy:
        constraints.append(Or(s + 30 <= start, s >= end))
    
    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[s].as_long()
        
        # Convert start time to HH:MM format
        start_hour = 9 + start_minutes // 60
        start_min = start_minutes % 60
        start_time = f"{start_hour}:{start_min:02d}"
        
        # Calculate and convert end time
        end_minutes = start_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_min = end_minutes % 60
        end_time = f"{end_hour}:{end_min:02d}"
        
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()