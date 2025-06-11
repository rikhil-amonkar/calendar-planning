from z3 import *

def main():
    # Brian's busy intervals in absolute minutes (from Monday 9:00)
    brian_busy = [
        (30, 60),      # Monday 9:30-10:00
        (210, 330),    # Monday 12:30-14:30
        (390, 420),    # Monday 15:30-16:00
        (480, 510),    # Tuesday 9:00-9:30
        (1170, 1260),  # Wednesday 12:30-14:00
        (1410, 1440),  # Wednesday 16:30-17:00
        (1560, 1590),  # Thursday 11:00-11:30
        (1680, 1710),  # Thursday 13:00-13:30
        (1890, 1920),  # Thursday 16:30-17:00
        (1950, 1980),  # Friday 9:30-10:00
        (2010, 2040),  # Friday 10:30-11:00
        (2160, 2190),  # Friday 13:00-13:30
        (2280, 2340),  # Friday 15:00-16:00
        (2370, 2400)   # Friday 16:30-17:00
    ]
    
    # Julia's busy intervals in absolute minutes (from Monday 9:00)
    julia_busy = [
        (0, 60),       # Monday 9:00-10:00
        (120, 150),    # Monday 11:00-11:30
        (210, 240),    # Monday 12:30-13:00
        (390, 420),    # Monday 15:30-16:00
        (720, 780),    # Tuesday 13:00-14:00
        (900, 930),    # Tuesday 16:00-16:30
        (960, 1110),   # Wednesday 9:00-11:30
        (1140, 1170),  # Wednesday 12:00-12:30
        (1200, 1440),  # Wednesday 13:00-17:00
        (1440, 1530),  # Thursday 9:00-10:30
        (1560, 1920),  # Thursday 11:00-17:00
        (1920, 1980),  # Friday 9:00-10:00
        (2010, 2070),  # Friday 10:30-11:30
        (2130, 2220),  # Friday 12:30-14:00
        (2250, 2280),  # Friday 14:30-15:00
        (2310, 2340)   # Friday 15:30-16:00
    ]
    
    # Combine all busy intervals
    busy_intervals = brian_busy + julia_busy
    
    # Initialize Z3 solver with optimization
    opt = Optimize()
    S = Int('S')
    
    # Constraints: S must be within the work week and allow a 60-minute meeting
    opt.add(S >= 0)
    opt.add(S <= 2340)  # 2400 - 60 (Friday 16:00 start)
    
    # Ensure meeting fits within a single workday (9:00-17:00)
    T = Int('T')
    opt.add(T == S % 480)
    opt.add(T <= 420)  # 480 - 60 minutes
    
    # Add non-overlap constraints with all busy intervals
    for start, end in busy_intervals:
        opt.add(Or(S + 60 <= start, S >= end))
    
    # Minimize S to find the earliest meeting time
    opt.minimize(S)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        start_abs = m[S].as_long()
        day_index = start_abs // 480
        days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
        day = days[day_index]
        
        # Calculate start time within the day
        T_val = start_abs % 480
        start_hour = 9 + T_val // 60
        start_minute = T_val % 60
        start_time = f"{start_hour}:{start_minute:02d}"
        
        # Calculate end time (60 minutes after start)
        end_minutes = T_val + 60
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour}:{end_minute:02d}"
        
        print(f"{day} {start_time} {end_time}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()