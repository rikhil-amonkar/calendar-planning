from z3 import *

def main():
    # Define the integer variables for day and start time (in minutes from 9:00)
    d = Int('d')
    s = Int('s')
    
    # Define the busy intervals in minutes from 9:00 for each day and participant
    laura_busy = {
        0: [(90, 120), (210, 240), (330, 390), (420, 480)],  # Monday
        1: [(30, 60), (120, 150), (240, 270), (330, 360), (420, 480)],  # Tuesday
        2: [(90, 120), (180, 270), (360, 390), (420, 450)]   # Thursday
    }
    
    philip_busy = {
        0: [(0, 480)],  # Monday (all day busy)
        1: [(0, 120), (150, 180), (240, 270), (300, 330), (360, 450)],  # Tuesday
        2: [(0, 90), (120, 210), (240, 480)]  # Thursday
    }
    
    solver = Solver()
    
    # Day must be 0 (Monday), 1 (Tuesday), or 2 (Thursday)
    solver.add(Or(d == 0, d == 1, d == 2))
    # Start time must be between 0 and 420 minutes (inclusive)
    solver.add(s >= 0, s <= 420)
    
    # For each day, add constraints based on busy intervals
    for day_idx in [0, 1, 2]:
        # Laura's constraints for the day
        laura_cons = []
        for (b_start, b_end) in laura_busy[day_idx]:
            # Meeting must end by the start of the busy interval or start after it ends
            laura_cons.append(Or(s + 60 <= b_start, s >= b_end))
        
        # Philip's constraints for the day
        philip_cons = []
        for (b_start, b_end) in philip_busy[day_idx]:
            philip_cons.append(Or(s + 60 <= b_start, s >= b_end))
        
        # Combine constraints: if current day, apply both Laura's and Philip's constraints
        all_cons = laura_cons + philip_cons
        solver.add(Implies(d == day_idx, And(all_cons)))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        day_idx = model[d].as_long()
        start_minutes = model[s].as_long()
        
        # Map day index to day name
        days = ['Monday', 'Tuesday', 'Thursday']
        day_str = days[day_idx]
        
        # Calculate start time (HH:MM)
        total_minutes = start_minutes
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_min = minutes
        
        # Calculate end time (start time + 60 minutes)
        end_minutes_total = start_minutes + 60
        end_hour = 9 + end_minutes_total // 60
        end_min = end_minutes_total % 60
        
        # Format to HH:MM
        start_time = f"{start_hour:02d}:{start_min:02d}"
        end_time = f"{end_hour:02d}:{end_min:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()