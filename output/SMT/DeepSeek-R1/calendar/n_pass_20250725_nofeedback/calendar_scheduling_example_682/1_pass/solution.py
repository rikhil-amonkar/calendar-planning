from z3 import *

def main():
    s = Solver()
    start = Int('start')
    
    # Meeting must be within 9:00 to 11:00 on Tuesday
    s.add(start >= 0)
    s.add(start + 30 <= 120)  # 30 minutes meeting, ending by 11:00 (120 minutes from 9:00)
    
    # Amanda's constraints: avoid 9:00-9:30 (0-30 minutes) and 10:00-10:30 (60-90 minutes)
    s.add(start >= 30)  # After 9:30
    s.add(Or(start >= 90, start + 30 <= 60))  # Avoid 10:00-10:30 by starting after 10:30 or ending before 10:00
    
    # Nathan's constraint: avoid 9:00-10:30 (0-90 minutes)
    s.add(start >= 90)  # After 10:30
    
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        
        # Convert minutes to time string
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        end_val = start_val + 30
        end_hours = 9 + end_val // 60
        end_minutes = end_val % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print("Day: Tuesday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()