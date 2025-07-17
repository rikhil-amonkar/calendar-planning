from z3 import *

def main():
    # Define the variables
    day = Int('day')
    start_time = Int('start_time')  # in minutes from 9:00

    # Create the optimizer
    opt = Optimize()

    # Constraints for day and start_time
    opt.add(day >= 0, day <= 3)
    opt.add(start_time >= 0, start_time <= 450)  # 450 + 30 = 480 (17:00)

    # Busy intervals for James per day (each interval is (start_minute, end_minute))
    intervals_per_day = [
        [ (0, 30), (90, 120), (210, 240), (330, 390), (450, 480) ],    # Monday (0)
        [ (0, 120), (150, 180), (210, 390), (420, 480) ],               # Tuesday (1)
        [ (60, 120), (180, 240), (270, 420) ],                           # Wednesday (2)
        [ (30, 150), (180, 210), (240, 270), (300, 330), (450, 480) ]   # Thursday (3)
    ]

    # Add constraints: for each day and each busy interval on that day, the meeting must not overlap
    for d, intervals in enumerate(intervals_per_day):
        for (s_busy, e_busy) in intervals:
            # The meeting is [start_time, start_time+30); it must not overlap [s_busy, e_busy)
            # So: either the meeting ends before the busy interval starts, or it starts after the busy interval ends.
            opt.add(Implies(day == d, Or(start_time + 30 <= s_busy, start_time >= e_busy)))

    # Set objectives: first minimize the day, then the start_time
    opt.minimize(day)
    opt.minimize(start_time)

    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        d_val = m[day].as_long()
        s_val = m[start_time].as_long()
        
        # Convert day value to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_name = days[d_val]
        
        # Convert start_time in minutes to time string
        total_minutes = s_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_minute = minutes
        start_str = f"{start_hour}:{start_minute:02d}"
        
        # Calculate end time
        end_val = s_val + 30
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60
        end_str = f"{end_hour}:{end_minute:02d}"
        
        # Print the result
        print(f"{day_name} {start_str} to {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()