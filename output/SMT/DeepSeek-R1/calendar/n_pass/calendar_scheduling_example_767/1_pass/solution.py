from z3 import Solver, Int, Or, If, And

def main():
    s = Solver()
    
    # Define variables
    d = Int('d')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_minutes = Int('start_minutes')  # minutes from 9:00
    
    # Constraints for day and start time
    s.add(d >= 0, d <= 2)
    s.add(start_minutes >= 0, start_minutes <= 420)  # 420 minutes = 7 hours -> 9:00 + 7h = 16:00, so meeting ends at 17:00
    
    # Martha's blocked intervals (day, start_min, end_min)
    martha_intervals = [
        (0, 420, 480),   # Monday: 16:00 to 17:00
        (1, 360, 390),   # Tuesday: 15:00 to 15:30
        (2, 60, 120),    # Wednesday: 10:00 to 11:00
        (2, 300, 330)    # Wednesday: 14:00 to 14:30
    ]
    
    # Beverly's blocked intervals
    beverly_intervals = [
        (0, 0, 270),     # Monday: 9:00 to 13:30
        (0, 300, 480),   # Monday: 14:00 to 17:00
        (1, 0, 480),     # Tuesday: entire day (9:00 to 17:00)
        (2, 30, 390),    # Wednesday: 9:30 to 15:30
        (2, 450, 480)    # Wednesday: 16:30 to 17:00
    ]
    
    # Add constraints for Martha's intervals
    for (day, s_start, s_end) in martha_intervals:
        s.add(If(d == day, Or(start_minutes + 60 <= s_start, start_minutes >= s_end), True)
    
    # Add constraints for Beverly's intervals
    for (day, s_start, s_end) in beverly_intervals:
        s.add(If(d == day, Or(start_minutes + 60 <= s_start, start_minutes >= s_end), True)
    
    # Check if a solution exists
    if s.check() == z3.sat:
        model = s.model()
        d_val = model[d].as_long()
        start_val = model[start_minutes].as_long()
        
        # Convert day value to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[d_val]
        
        # Calculate start time in HH:MM
        total_minutes = start_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_min = minutes
        start_time = f"{start_hour:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_val + 60
        end_hour = 9 + end_minutes // 60
        end_min = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_min:02d}"
        
        # Print solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()