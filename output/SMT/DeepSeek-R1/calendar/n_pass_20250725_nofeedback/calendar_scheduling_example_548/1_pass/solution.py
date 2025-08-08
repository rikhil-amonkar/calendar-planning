from z3 import *

def main():
    # Define the start time variable in minutes from 9:00
    s = Int('s')
    
    # Define the constraints for the free slots of Nicole
    # Free slot 1: 10:00 to 10:30 -> [60, 90] -> meeting must start at 60 and end at 90 (so s must be 60)
    # Free slot 2: 16:30 to 17:00 -> [450, 480] -> meeting must start at 450 and end at 480 (so s must be 450)
    hard_constraint = Or(
        And(s >= 60, s + 30 <= 90),   # This simplifies to s=60
        And(s >= 450, s + 30 <= 480)   # This simplifies to s=450
    )
    
    # Create an optimizer
    opt = Optimize()
    opt.add(hard_constraint)
    
    # Add soft constraint for Nicole's preference: meeting should start at or after 16:00 (420 minutes from 9:00)
    opt.add_soft(s >= 420)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        start_min = m[s].as_long()
        
        # Convert start time from minutes to time string
        total_minutes = start_min
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_time = f"{start_hour:02d}:{minutes:02d}"
        
        # Calculate end time
        end_min = start_min + 30
        end_hours = end_min // 60
        end_minutes = end_min % 60
        end_hour = 9 + end_hours
        end_time = f"{end_hour:02d}:{end_minutes:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()