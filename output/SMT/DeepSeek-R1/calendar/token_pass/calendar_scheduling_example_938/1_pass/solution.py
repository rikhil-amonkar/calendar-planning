from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define variables: day (0=Mon, 1=Tue, 2=Wed, 3=Thu, 4=Fri) and start time in minutes from 9:00
    day = Int('day')
    start = Int('start')
    
    # Define constraints for day and start time
    s.add(day >= 0, day <= 4)
    s.add(start >= 0, start <= 450)  # 450 = 17:00 - 30 minutes
    
    # Define busy intervals for each day (merged where possible)
    busy_intervals = {
        0: [(0, 480)],  # Monday entirely busy
        1: [(0, 480)],  # Tuesday entirely busy
        2: [(0, 150), (180, 360), (330, 450)],  # Wednesday merged intervals
        3: [(0, 480)],  # Thursday entirely busy
        4: [(0, 120), (150, 480)]  # Friday merged intervals
    }
    
    # Add constraints: for the selected day, meeting must not overlap any busy interval
    for d, intervals in busy_intervals.items():
        for busystart, busyend in intervals:
            s.add(If(day == d, Or(start + 30 <= busystart, start >= busyend), True))
    
    # First try to avoid Wednesday (day != 2)
    s.push()
    s.add(day != 2)
    if s.check() == sat:
        model = s.model()
    else:
        s.pop()
        # If no solution without Wednesday, allow Wednesday
        s.check()
        model = s.model()
    
    # Get the solution
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    
    # Map day index to day name
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_name = days[day_val]
    
    # Calculate start and end times
    start_hour = 9 + start_val // 60
    start_minute = start_val % 60
    end_minutes = start_val + 30
    end_hour = 9 + end_minutes // 60
    end_minute = end_minutes % 60
    
    # Format the output
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    print(f"{day_name} {time_str}")

if __name__ == "__main__":
    main()