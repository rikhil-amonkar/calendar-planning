from z3 import *

def main():
    # Define busy intervals in minutes from 9:00
    carl_busy = {
        0: [(120, 150)],  # Monday: 11:00-11:30
        1: [(330, 360)],  # Tuesday: 14:30-15:00
        2: [(60, 150), (240, 270)],  # Wednesday: 10:00-11:30, 13:00-13:30
        3: [(270, 300), (420, 450)]  # Thursday: 13:30-14:00, 16:00-16:30
    }
    
    margaret_busy = {
        0: [(0, 90), (120, 480)],  # Monday: 9:00-10:30, 11:00-17:00
        1: [(30, 180), (270, 300), (390, 480)],  # Tuesday: 9:30-12:00, 13:30-14:00, 15:30-17:00
        2: [(30, 180), (210, 240), (270, 330), (360, 480)],  # Wednesday: 9:30-12:00, 12:30-13:00, 13:30-14:30, 15:00-17:00
        3: [(60, 180), (210, 300), (330, 480)]  # Thursday: 10:00-12:00, 12:30-14:00, 14:30-17:00
    }
    
    s = Solver()
    day = Int('day')
    start = Int('start')
    
    # Day must be between 0 (Monday) and 3 (Thursday)
    s.add(day >= 0, day <= 3)
    # Start time must be between 0 (9:00) and 420 (16:00) to allow a 60-minute meeting ending by 17:00
    s.add(start >= 0, start <= 420)
    
    # Add constraints for each day
    for d in range(4):
        # Carl's busy intervals for day d
        for b_start, b_end in carl_busy[d]:
            s.add(Implies(day == d, Or(start + 60 <= b_start, start >= b_end)))
        # Margaret's busy intervals for day d
        for b_start, b_end in margaret_busy[d]:
            s.add(Implies(day == d, Or(start + 60 <= b_start, start >= b_end)))
    
    # First, try to avoid Thursday (day 3)
    s_temp = Solver()
    s_temp.add(s.assertions())
    s_temp.add(day != 3)
    
    if s_temp.check() == sat:
        m = s_temp.model()
    else:
        # If no solution without Thursday, try with Thursday allowed
        if s.check() == sat:
            m = s.model()
        else:
            print("No solution found")
            return
    
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    
    # Convert day index to day name
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_name = days[day_val]
    
    # Convert start minutes to time string
    total_minutes = start_val
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{9 + hours}:{minutes:02d}" if minutes > 0 else f"{9 + hours}:00"
    
    # Calculate end time
    end_minutes = start_val + 60
    end_hours = 9 + end_minutes // 60
    end_minutes %= 60
    end_time = f"{end_hours}:{end_minutes:02d}" if end_minutes > 0 else f"{end_hours}:00"
    
    print(f"Day: {day_name}")
    print(f"Start: {start_time}")
    print(f"End: {end_time}")

if __name__ == "__main__":
    main()