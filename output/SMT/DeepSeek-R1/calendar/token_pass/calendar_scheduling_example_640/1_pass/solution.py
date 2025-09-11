from z3 import *

def main():
    # Define the start time variable in minutes from Monday 9:00 (0) to Tuesday 17:00 (960)
    S = Int('S')
    opt = Optimize()
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Define the valid time segments for Monday and Tuesday
    monday_segment = And(S >= 0, S <= 450)  # Monday 9:00 to 16:30 (since 16:30 + 30 = 17:00)
    tuesday_segment = And(S >= 480, S <= 930) # Tuesday 9:00 to 16:30 (shifted by 480 minutes)
    time_constraint = Or(monday_segment, tuesday_segment)
    
    # Bobby's busy intervals in minutes from Monday 9:00
    bobby_busy = [
        (330, 360),   # Monday 14:30-15:00
        (480, 630),   # Tuesday 9:00-11:30
        (660, 690),   # Tuesday 12:00-12:30
        (720, 840),   # Tuesday 13:00-15:00
        (870, 960)    # Tuesday 15:30-17:00
    ]
    
    # Michael's busy intervals in minutes from Monday 9:00
    michael_busy = [
        (0, 60),      # Monday 9:00-10:00
        (90, 270),    # Monday 10:30-13:30
        (300, 360),   # Monday 14:00-15:00
        (390, 480),   # Monday 15:30-17:00
        (480, 570),   # Tuesday 9:00-10:30
        (600, 630),   # Tuesday 11:00-11:30
        (660, 780),   # Tuesday 12:00-14:00
        (840, 900),   # Tuesday 15:00-16:00
        (930, 960)    # Tuesday 16:30-17:00
    ]
    
    # Add constraints for Bobby's availability
    for start, end in bobby_busy:
        opt.add(Or(S + meeting_duration <= start, S >= end))
    
    # Add constraints for Michael's availability
    for start, end in michael_busy:
        opt.add(Or(S + meeting_duration <= start, S >= end))
    
    # Add the time constraint
    opt.add(time_constraint)
    
    # Minimize S to find the earliest time
    opt.minimize(S)
    
    if opt.check() == sat:
        m = opt.model()
        s_val = m.eval(S).as_long()
        
        # Determine the day and adjust time accordingly
        if s_val <= 450:
            day = "Monday"
            start_time = s_val
        else:
            day = "Tuesday"
            start_time = s_val - 480
        
        # Calculate start hour and minute
        start_hour = 9 + start_time // 60
        start_minute = start_time % 60
        end_time = start_time + meeting_duration
        end_hour = 9 + end_time // 60
        end_minute = end_time % 60
        
        # Format the output
        print(f"{day} {start_hour}:{start_minute:02d}:{end_hour}:{end_minute:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()