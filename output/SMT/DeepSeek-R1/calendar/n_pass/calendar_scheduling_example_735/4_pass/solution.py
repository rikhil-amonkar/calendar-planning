from z3 import *

def main():
    # Convert busy times to minutes from 9:00
    ronald_busy = {
        "Monday": [(90, 120), (180, 210), (390, 420)],
        "Tuesday": [(0, 30), (180, 210), (390, 450)],
        "Wednesday": [(30, 90), (120, 180), (210, 240), (270, 300), (450, 480)]
    }
    
    amber_busy = {
        "Monday": [(0, 30), (60, 90), (150, 180), (210, 300), (330, 360), (390, 480)],
        "Tuesday": [(0, 30), (60, 150), (180, 210), (270, 390), (450, 480)],
        "Wednesday": [(0, 30), (60, 90), (120, 270), (360, 390)]
    }
    
    days = ["Monday", "Tuesday", "Wednesday"]
    
    # Create Z3 variables
    day_var = Int('day')
    start_var = Int('start')
    
    # Create solver with optimization
    s = Optimize()
    
    # Day must be 0, 1, or 2
    s.add(day_var >= 0, day_var <= 2)
    # Start time must allow 30-minute meeting before 17:00
    s.add(start_var >= 0, start_var <= 450)
    
    # For each day, add non-overlap constraints
    for d in range(3):
        day_name = days[d]
        constraints = []
        
        # Ronald's constraints for this day
        for block in ronald_busy[day_name]:
            block_start, block_end = block
            # Meeting must be before or after the block
            constraints.append(Or(start_var + 30 <= block_start, start_var >= block_end))
        
        # Amber's constraints for this day
        for block in amber_busy[day_name]:
            block_start, block_end = block
            constraints.append(Or(start_var + 30 <= block_start, start_var >= block_end))
        
        # Apply constraints only if meeting is on this day
        s.add(Implies(day_var == d, And(constraints)))
    
    # Minimize day and start time for earliest availability
    s.minimize(day_var * 1000 + start_var)
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day_var].as_long()
        start_minutes = m[start_var].as_long()
        
        day_name = days[d_val]
        # Convert minutes to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes %= 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()