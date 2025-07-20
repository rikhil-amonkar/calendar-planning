from z3 import *

def main():
    # Create solver and variables
    day = Int('day')
    start = Int('start')
    end = start + 30  # Meeting duration is 30 minutes

    s = Optimize()
    
    # Day must be either Monday (0) or Tuesday (1)
    s.add(Or(day == 0, day == 1))
    
    # Meeting must be within 9:00 to 17:00 (0 to 480 minutes)
    s.add(start >= 0)
    s.add(end <= 480)
    
    # Monday: Albert is busy from 9:00 to 17:00 (entire day)
    # This makes scheduling on Monday impossible
    s.add(Implies(day == 0, Or(end <= 0, start >= 480)))
    
    # Tuesday constraints
    # Avoid Shirley's busy interval: [30, 60) (9:30 to 10:00)
    # Avoid Albert's busy intervals: [30, 120), [150, 210), [240, 420), [450, 480)
    s.add(Implies(day == 1, 
                And(
                    Or(end <= 30, start >= 60),    # Avoid Shirley's busy [30,60)
                    Or(end <= 30, start >= 120),   # Avoid Albert's [30,120)
                    Or(end <= 150, start >= 210),  # Avoid Albert's [150,210)
                    Or(end <= 240, start >= 420),  # Avoid Albert's [240,420)
                    end <= 450                    # Avoid Albert's [450,480)
                )))
    
    # Minimize (day * 10000 + start) to get earliest day and earliest start time
    s.minimize(day * 10000 + start)
    
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        st_val = m[start].as_long()
        
        # Convert start time from minutes to HH:MM format
        total_minutes = st_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_time = f"{start_hour:02d}:{minutes:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_minutes = st_val + 30
        end_hours = end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_hour = 9 + end_hours
        end_time = f"{end_hour:02d}:{end_minutes_remainder:02d}"
        
        day_str = "Monday" if d == 0 else "Tuesday"
        
        # Print solution in required format
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()