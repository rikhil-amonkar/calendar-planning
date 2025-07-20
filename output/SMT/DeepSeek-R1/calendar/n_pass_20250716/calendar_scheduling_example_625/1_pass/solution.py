from z3 import *

def main():
    # Define variables
    day = Int('day')
    start_minutes = Int('start_minutes')  # Minutes from 9:00 on the chosen day

    s = Solver()

    # Day must be 0 (Monday) or 1 (Tuesday)
    s.add(Or(day == 0, day == 1))
    
    # Start time constraints: 0 minutes (9:00) to 450 minutes (16:30) since meeting is 30 minutes until 17:00
    s.add(start_minutes >= 0)
    s.add(start_minutes <= 450)  # 480 - 30 = 450
    
    # Constraints based on Harold's existing schedule
    # Monday: free only from 10:00 to 10:30 (60 to 90 minutes from 9:00)
    monday_ok = And(day == 0, start_minutes >= 60, start_minutes + 30 <= 90)
    
    # Tuesday: free intervals
    tuesday_ok = And(day == 1, 
                      Or(And(start_minutes >= 30, start_minutes + 30 <= 90),    # 9:30-10:00
                         And(start_minutes >= 150, start_minutes + 30 <= 210),  # 11:30-12:00
                         And(start_minutes >= 180, start_minutes + 30 <= 210),  # 12:00-12:30
                         And(start_minutes >= 270, start_minutes + 30 <= 330),  # 13:30-14:00
                         And(start_minutes >= 300, start_minutes + 30 <= 330),  # 14:00-14:30
                         And(start_minutes >= 390, start_minutes + 30 <= 420)   # 15:30-16:00
                      ))
    
    s.add(Or(monday_ok, tuesday_ok))
    
    # Harold's preferences: avoid Monday and Tuesday before 14:30 (330 minutes from 9:00)
    s.add(day != 0)  # Avoid Monday
    # For Tuesday, ensure meeting starts at or after 14:30 (330 minutes)
    s.add(If(day == 1, start_minutes >= 330, True))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        st_minutes = m[start_minutes].as_long()
        
        # Convert minutes to time string
        hours = st_minutes // 60
        minutes = st_minutes % 60
        start_time = f"{9 + hours}:{minutes:02d}"
        
        end_minutes = st_minutes + 30
        end_hours = end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time = f"{9 + end_hours}:{end_minutes_remainder:02d}"
        
        day_str = "Monday" if d == 0 else "Tuesday"
        print(f"Day: {day_str}")
        print(f"Start: {start_time}")
        print(f"End: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()