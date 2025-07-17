from z3 import *

def main():
    # Create the solver
    s = Solver()
    
    # Define variables
    day = Int('day')
    start_min = Int('start_min')
    
    # Hard constraints: day in [0,2] and start_min in [0,420]
    s.add(day >= 0, day <= 2)
    s.add(start_min >= 0, start_min <= 420)
    
    # Define busy intervals for each day (in minutes from 9:00)
    mon_busy = [(30,60), (90,150), (180,210), (210,300), (390,480)]
    tue_busy = [(30,240), (270,300), (330,480)]
    wed_busy = [(0,30), (90,120), (150,180), (270,330), (360,390), (420,450)]
    
    # Add constraints for each day's busy intervals
    for (s_busy, e_busy) in mon_busy:
        s.add(If(day == 0, Or(start_min + 60 <= s_busy, start_min >= e_busy), True))
    for (s_busy, e_busy) in tue_busy:
        s.add(If(day == 1, Or(start_min + 60 <= s_busy, start_min >= e_busy), True))
    for (s_busy, e_busy) in wed_busy:
        s.add(If(day == 2, Or(start_min + 60 <= s_busy, start_min >= e_busy), True))
    
    # Define and apply preference constraints (soft constraints)
    s.push()
    s.add(day != 0)  # Avoid Monday
    s.add(If(day == 2, start_min >= 180, True))  # On Wednesday, avoid before 12:00
    
    # Check for solution with preferences
    if s.check() == sat:
        m = s.model()
    else:
        # No solution with preferences, revert to hard constraints only
        s.pop()
        s.check()
        m = s.model()
    
    # Extract solution values
    day_val = m[day].as_long()
    start_min_val = m[start_min].as_long()
    
    # Convert day value to string
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[day_val]
    
    # Calculate start time in HH:MM format
    total_minutes_start = start_min_val
    start_hour = 9 + total_minutes_start // 60
    start_minute = total_minutes_start % 60
    start_time = f"{start_hour:02d}:{start_minute:02d}"
    
    # Calculate end time (start time + 60 minutes)
    total_minutes_end = total_minutes_start + 60
    end_hour = 9 + total_minutes_end // 60
    end_minute = total_minutes_end % 60
    end_time = f"{end_hour:02d}:{end_minute:02d}"
    
    # Output the solution in the required format
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()