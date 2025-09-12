from z3 import *

def main():
    # Define the day and start time variables
    day = Int('day')
    start_time = Int('start_time')
    
    s = Solver()
    
    # Day constraint: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    s.add(day >= 0, day <= 3)
    
    # Start time constraint: 9:00 to 16:00 in minutes from 9:00 (0 to 420 minutes)
    s.add(start_time >= 0, start_time <= 420)
    
    # Convert busy times to minutes from 9:00
    carl_busy = {
        0: [(120, 150)],  # Monday 11:00-11:30
        1: [(330, 360)],  # Tuesday 14:30-15:00
        2: [(60, 150), (240, 270)],  # Wednesday 10:00-11:30, 13:00-13:30
        3: [(270, 300), (420, 450)]   # Thursday 13:30-14:00, 16:00-16:30
    }
    
    margaret_busy = {
        0: [(0, 90), (120, 480)],  # Monday 9:00-10:30, 11:00-17:00
        1: [(30, 180), (270, 300), (390, 480)],  # Tuesday 9:30-12:00, 13:30-14:00, 15:30-17:00
        2: [(30, 180), (210, 240), (270, 330), (360, 480)],  # Wednesday 9:30-12:00, 12:30-13:00, 13:30-14:30, 15:00-17:00
        3: [(60, 180), (210, 300), (330, 480)]  # Thursday 10:00-12:00, 12:30-14:00, 14:30-17:00
    }
    
    # Create constraints for each day
    days = [0, 1, 2, 3]
    for d in days:
        constraints = []
        # Carl's constraints for day d
        for interval in carl_busy.get(d, []):
            constraints.append(Or(start_time + 60 <= interval[0], start_time >= interval[1]))
        # Margaret's constraints for day d
        for interval in margaret_busy.get(d, []):
            constraints.append(Or(start_time + 60 <= interval[0], start_time >= interval[1]))
        # If meeting is on day d, apply constraints
        s.add(If(day == d, And(constraints), True))
    
    # Prefer non-Thursday days
    s.push()
    s.add(day != 3)
    
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
    else:
        s.pop()
        s.check()
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
    
    # Convert start time to HH:MM format
    start_hour = 9 + start_val // 60
    start_minute = start_val % 60
    end_val = start_val + 60
    end_hour = 9 + end_val // 60
    end_minute = end_val % 60
    
    day_names = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    print(f"{day_names[day_val]}: {start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")

if __name__ == "__main__":
    main()