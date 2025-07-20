from z3 import *

def main():
    # Convert busy times to minutes from 9:00
    # Monday
    ryan_busy_m = [(30,60), (120,180), (240,270), (390,420)]
    adam_busy_m = [(0,90), (120,270), (300,420), (450,480)]
    # Tuesday
    ryan_busy_t = [(150,210), (390,420)]
    adam_busy_t = [(0,60), (90,390), (420,480)]
    
    # Create solver and variables
    day = Int('day')
    start = Int('start')
    
    # Domain constraints
    constraints = [
        Or(day == 0, day == 1),
        start >= 0,
        start <= 450  # because 17:00 is 480 minutes, 480-30=450
    ]
    
    # Monday constraints: not overlapping with any busy interval for Ryan or Adam
    monday_constraints = []
    for s, e in ryan_busy_m:
        monday_constraints.append(Or(start + 30 <= s, start >= e))
    for s, e in adam_busy_m:
        monday_constraints.append(Or(start + 30 <= s, start >= e))
    monday_case = And(day == 0, *monday_constraints)
    
    # Tuesday constraints
    tuesday_constraints = []
    for s, e in ryan_busy_t:
        tuesday_constraints.append(Or(start + 30 <= s, start >= e))
    for s, e in adam_busy_t:
        tuesday_constraints.append(Or(start + 30 <= s, start >= e))
    tuesday_case = And(day == 1, *tuesday_constraints)
    
    # Overall constraint: either Monday or Tuesday works
    constraints.append(Or(monday_case, tuesday_case))
    
    # Preference constraint: avoid Monday before 14:30 (330 minutes from 9:00)
    preference = Or(day != 0, start >= 330)
    
    # First try with preference
    s1 = Solver()
    s1.add(constraints)
    s1.add(preference)
    
    if s1.check() == sat:
        m = s1.model()
    else:
        s2 = Solver()
        s2.add(constraints)
        if s2.check() == sat:
            m = s2.model()
        else:
            print("No solution found")
            return

    d = m[day].as_long()
    st_val = m[start].as_long()
    
    # Convert start time to HH:MM
    total_minutes_start = st_val
    start_hour = 9 + total_minutes_start // 60
    start_minute = total_minutes_start % 60
    start_time_str = f"{start_hour:02d}:{start_minute:02d}"
    
    # End time is start time + 30 minutes
    total_minutes_end = st_val + 30
    end_hour = 9 + total_minutes_end // 60
    end_minute = total_minutes_end % 60
    end_time_str = f"{end_hour:02d}:{end_minute:02d}"
    
    day_str = "Monday" if d == 0 else "Tuesday"
    
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")

if __name__ == "__main__":
    main()