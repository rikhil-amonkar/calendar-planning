from z3 import *

def main():
    # Define the variables
    d = Int('d')  # day: 0 for Monday, 2 for Wednesday
    s = Int('s')  # start time in minutes from midnight

    # Create the solver with optimization
    solver = Optimize()
    
    # Day must be either Monday (0) or Wednesday (2)
    solver.add(Or(d == 0, d == 2))
    
    # Meeting must start at or after 9:00 (540 minutes) and end by 17:00 (1020 minutes)
    solver.add(s >= 540)       # 9:00 in minutes
    solver.add(s + 30 <= 1020) # Meeting ends by 17:00 (1020 minutes)
    
    # Define busy intervals in minutes from midnight
    arthur_mon = [(660, 690), (810, 840), (900, 930)]  # Monday meetings for Arthur
    michael_mon = [(540, 720), (750, 780), (840, 870), (900, 1020)]  # Monday meetings for Michael
    
    arthur_wed = [(600, 630), (660, 690), (720, 750), (840, 870), (960, 990)]  # Wednesday meetings for Arthur
    michael_wed = [(600, 750), (780, 810)]  # Wednesday meetings for Michael
    
    # Add constraints for Monday: if d==0, the meeting must not overlap with any of Arthur's or Michael's meetings
    for (start_busy, end_busy) in arthur_mon:
        solver.add(Implies(d == 0, Or(s + 30 <= start_busy, s >= end_busy)))
    for (start_busy, end_busy) in michael_mon:
        solver.add(Implies(d == 0, Or(s + 30 <= start_busy, s >= end_busy)))
    
    # Add constraints for Wednesday: if d==2, the meeting must not overlap with any of Arthur's or Michael's meetings
    for (start_busy, end_busy) in arthur_wed:
        solver.add(Implies(d == 2, Or(s + 30 <= start_busy, s >= end_busy)))
    for (start_busy, end_busy) in michael_wed:
        solver.add(Implies(d == 2, Or(s + 30 <= start_busy, s >= end_busy)))
    
    # Minimize total minutes from start of the week (Monday 00:00) to meeting start time
    total_minutes = d * 24 * 60 + s
    solver.minimize(total_minutes)
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        day_val = model[d].as_long()
        start_minutes = model[s].as_long()
        
        # Convert day value to day name
        day_str = "Monday" if day_val == 0 else "Wednesday"
        
        # Convert start time to HH:MM format
        hour = start_minutes // 60
        minute = start_minutes % 60
        start_time = f"{hour:02d}:{minute:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_minutes = start_minutes + 30
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution in the required format
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()