from z3 import *

def main():
    # Initialize solver
    solver = Solver()
    
    # Define variables
    day = Int('day')
    start = Int('start')
    
    # Day constraints: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
    solver.add(day >= 0, day <= 4)
    solver.add(day != 2, day != 3)  # Betty cannot meet on Wednesday or Thursday
    
    # Meeting duration (60 minutes) and work hours (9:00 to 17:00 -> 0 to 480 minutes)
    solver.add(start >= 0, start <= 420)  # Latest start: 420 (16:00) for 60min meeting
    
    # Betty's busy intervals (minutes from 9:00)
    betty_busy = {
        0: [(60, 90), (150, 210), (420, 450)],    # Monday
        1: [(30, 60), (90, 120), (180, 210), (270, 360), (450, 480)],  # Tuesday
        4: [(0, 60), (150, 180), (210, 240), (270, 300)]  # Friday
    }
    
    # Megan's busy intervals (minutes from 9:00)
    megan_busy = {
        0: [(0, 480)],  # Monday
        1: [(0, 30), (60, 90), (180, 300), (360, 390), (420, 450)],  # Tuesday
        2: [(30, 90), (120, 150), (210, 240), (270, 330), (390, 480)],  # Wednesday
        3: [(0, 90), (150, 300), (330, 360), (390, 450)],  # Thursday
        4: [(0, 480)]   # Friday
    }
    
    # Function to generate no-overlap constraints
    def no_overlap(busy_list, s):
        return And([Or(s + 60 <= start_busy, s >= end_busy) for (start_busy, end_busy) in busy_list])
    
    # Add constraints for Betty
    for d, intervals in betty_busy.items():
        solver.add(If(day == d, no_overlap(intervals, start), True))
        
    # Add constraints for Megan
    for d, intervals in megan_busy.items():
        solver.add(If(day == d, no_overlap(intervals, start), True))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        d_val = model[day].as_long()
        start_val = model[start].as_long()
        
        # Convert start time to HH:MM format
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = total_minutes + 60
        end_hours = 9 + end_minutes // 60
        end_minutes %= 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Map day value to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_str = days[d_val]
        
        # Print result
        print(f"{start_str}:{end_str}")
        print(day_str)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()