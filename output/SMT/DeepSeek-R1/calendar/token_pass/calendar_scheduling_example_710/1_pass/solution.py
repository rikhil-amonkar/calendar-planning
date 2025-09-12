from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define variables: day (0=Monday, 1=Tuesday) and slot index (0-15 for 9:00-17:00 in 30-min intervals)
    day = Int('day')
    slot = Int('slot')
    
    # Constrain day to Monday or Tuesday (Wednesday is excluded due to Cheryl's constraint)
    solver.add(Or(day == 0, day == 1))
    solver.add(slot >= 0, slot <= 15)
    
    # Define busy slots for each participant per day
    cheryl_busy_monday = [0, 5, 6, 7, 13]
    cheryl_busy_tuesday = [12]
    kyle_busy_monday = list(range(0, 16))  # All slots busy
    kyle_busy_tuesday = list(range(1, 16)) # Only slot 0 is free
    
    # Constraints: The meeting must be when both participants are free
    # For Monday (day 0)
    monday_constraint = And(
        day == 0,
        Not(Or([slot == i for i in cheryl_busy_monday])),
        Not(Or([slot == i for i in kyle_busy_monday]))
    )
    
    # For Tuesday (day 1)
    tuesday_constraint = And(
        day == 1,
        Not(Or([slot == i for i in cheryl_busy_tuesday])),
        Not(Or([slot == i for i in kyle_busy_tuesday]))
    )
    
    solver.add(Or(monday_constraint, tuesday_constraint))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        d = model[day].as_long()
        s = model[slot].as_long()
        
        # Map day index to name
        days = ["Monday", "Tuesday"]
        day_name = days[d]
        
        # Calculate start and end times from slot index
        start_minutes = 9 * 60 + s * 30
        end_minutes = start_minutes + 30
        start_time = f"{start_minutes // 60:02d}:{start_minutes % 60:02d}"
        end_time = f"{end_minutes // 60:02d}:{end_minutes % 60:02d}"
        
        print(f"{day_name} {start_time}:{end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()