from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define variables
    day = Int('day')
    start = Int('start')
    
    # Constraints for day: only Wednesday (2) or Friday (4)
    s.add(Or(day == 2, day == 4))
    # Constraints for start: between 0 and 420 minutes (9:00 to 16:00 inclusive)
    s.add(start >= 0, start <= 420)
    
    # Busy intervals for Wednesday (only Nicholas)
    wed_nicholas_busy = [
        (0, 30),    # 9:00-9:30
        (60, 120),  # 10:00-11:00
        (150, 270), # 11:30-13:30
        (300, 330), # 14:00-14:30
        (360, 450)  # 15:00-16:30
    ]
    
    # Busy intervals for Friday (Bryan and Nicholas)
    fri_bryan_busy = [
        (90, 120),  # 10:30-11:00
        (300, 330)  # 14:00-14:30
    ]
    fri_nicholas_busy = [
        (0, 90),    # 9:00-10:30
        (120, 180), # 11:00-12:00
        (210, 330), # 12:30-14:30
        (390, 420)  # 15:30-16:00
    ]
    
    # Add constraints for Wednesday
    for s_val, e_val in wed_nicholas_busy:
        s.add(If(day == 2, Or(start + 60 <= s_val, start >= e_val), True))
    
    # Add constraints for Friday (Bryan)
    for s_val, e_val in fri_bryan_busy:
        s.add(If(day == 4, Or(start + 60 <= s_val, start >= e_val), True))
    
    # Add constraints for Friday (Nicholas)
    for s_val, e_val in fri_nicholas_busy:
        s.add(If(day == 4, Or(start + 60 <= s_val, start >= e_val), True))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_val = model[start].as_long()
        
        # Convert start time to HH:MM
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = total_minutes + 60
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Map day value to day name
        day_map = {2: "Wednesday", 4: "Friday"}
        day_name = day_map[day_val]
        
        # Print solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()