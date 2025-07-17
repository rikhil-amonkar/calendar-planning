from z3 import *

def main():
    # Initialize the solver
    s = Solver()
    
    # Define the variables: day (0 for Monday, 1 for Tuesday) and start time in minutes from 9:00
    day = Int('day')
    start_minutes = Int('start_minutes')
    
    # Constraints for day: must be 0 or 1
    s.add(Or(day == 0, day == 1))
    # Constraints for start_minutes: must be between 0 (9:00) and 420 (16:00)
    s.add(start_minutes >= 0)
    s.add(start_minutes <= 420)  # 420 minutes = 7 hours, so 16:00 is the latest start
    
    # Patricia's busy intervals in minutes from 9:00
    patricia_monday = [
        (60, 90),    # 10:00-10:30
        (150, 180),  # 11:30-12:00
        (240, 270),  # 13:00-13:30
        (330, 390),  # 14:30-15:30
        (420, 450)   # 16:00-16:30
    ]
    patricia_tuesday = [
        (60, 90),    # 10:00-10:30
        (120, 180),  # 11:00-12:00
        (300, 420),  # 14:00-16:00
        (450, 480)   # 16:30-17:00
    ]
    
    # Jesse's busy intervals in minutes from 9:00
    jesse_monday = [
        (0, 480)     # Entire day blocked (9:00-17:00)
    ]
    jesse_tuesday = [
        (120, 150),  # 11:00-11:30
        (180, 210),  # 12:00-12:30
        (240, 300),  # 13:00-14:00
        (330, 360),  # 14:30-15:00
        (390, 480)   # 15:30-17:00
    ]
    
    # Function to add constraints for a participant's busy intervals
    def add_busy_constraints(busy_intervals, day_val):
        constraints = []
        for (busy_start, busy_end) in busy_intervals:
            # The meeting must not overlap with any busy interval: either ends before the busy interval starts or starts after it ends
            constraints.append(Or(day != day_val, 
                                  start_minutes + 60 <= busy_start, 
                                  start_minutes >= busy_end))
        s.add(constraints)
    
    # Add constraints for Patricia and Jesse for both days
    add_busy_constraints(patricia_monday, 0)
    add_busy_constraints(patricia_tuesday, 1)
    add_busy_constraints(jesse_monday, 0)
    add_busy_constraints(jesse_tuesday, 1)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        d = model[day].as_long()
        start_min = model[start_minutes].as_long()
        
        # Convert start_min to time string
        total_minutes = start_min
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_time = f"{start_hour:02d}:{minutes:02d}"
        
        # Calculate end time (start_min + 60 minutes)
        end_min = total_minutes + 60
        end_hours = end_min // 60
        end_minutes = end_min % 60
        end_hour = 9 + end_hours
        end_time = f"{end_hour:02d}:{end_minutes:02d}"
        
        # Map day value to day name
        day_name = "Monday" if d == 0 else "Tuesday"
        
        # Print solution in required format
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()