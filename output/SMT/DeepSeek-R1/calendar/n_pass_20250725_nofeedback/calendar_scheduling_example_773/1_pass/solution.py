from z3 import *

def main():
    # Create solver
    opt = Optimize()
    
    # Day: 0 = Monday, 1 = Tuesday, 2 = Wednesday
    day = Int('day')
    start_minutes = Int('start_minutes')  # minutes from 9:00 on the chosen day
    
    # Constraints for day and start_minutes
    opt.add(day >= 0)
    opt.add(day <= 2)
    opt.add(start_minutes >= 0)
    opt.add(start_minutes <= 420)  # because 480 - 60 = 420
    
    # Busy intervals in minutes from 9:00 (each interval is [start, end))
    Monday_busy = [(60, 150), (180, 240), (300, 330), (360, 480)]
    Tuesday_busy = [(90, 150), (180, 330), (360, 390), (420, 480)]
    Wednesday_busy = [(30, 150), (210, 300), (330, 390), (450, 480)]
    
    # For each day, add constraints that the meeting does not overlap with any busy interval
    for idx, day_busy in enumerate([Monday_busy, Tuesday_busy, Wednesday_busy]):
        for (s_busy, e_busy) in day_busy:
            # If the meeting is on this day, it must not overlap with this busy interval
            opt.add(Implies(day == idx, Or(start_minutes + 60 <= s_busy, start_minutes >= e_busy)))
    
    # Minimize total minutes from Monday 9:00
    total_minutes = day * 480 + start_minutes
    opt.minimize(total_minutes)
    
    # Check for solution
    if opt.check() == sat:
        m = opt.model()
        d_val = m[day].as_long()
        s_val = m[start_minutes].as_long()
        
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[d_val]
        
        # Calculate start time
        start_hour = 9 + s_val // 60
        start_minute = s_val % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time (start time + 60 minutes)
        end_minutes = s_val + 60
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()