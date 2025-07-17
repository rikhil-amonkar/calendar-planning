from z3 import *

def main():
    # Day mapping: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Busy intervals in minutes from 9:00 (start of the workday)
    mary_busy = {
        1: [(60, 90), (390, 420)],   # Tuesday: 10:00-10:30, 15:30-16:00
        2: [(30, 60), (360, 390)],   # Wednesday: 9:30-10:00, 15:00-15:30
        3: [(0, 60), (90, 150)]      # Thursday: 9:00-10:00, 10:30-11:30
    }
    
    alexis_busy = {
        0: [(0, 60), (90, 180), (210, 450)],   # Monday: 9:00-10:00, 10:30-12:00, 12:30-16:30
        1: [(0, 60), (90, 150), (180, 390), (420, 480)],  # Tuesday: 9:00-10:00, 10:30-11:30, 12:00-15:30, 16:00-17:00
        2: [(0, 120), (150, 480)],   # Wednesday: 9:00-11:00, 11:30-17:00
        3: [(60, 180), (300, 330), (390, 420), (450, 480)]  # Thursday: 10:00-12:00, 14:00-14:30, 15:30-16:00, 16:30-17:00
    }
    
    # Initialize Z3 variables
    day_var = Int('day')
    start_var = Int('start')
    
    # Initialize optimizer
    opt = Optimize()
    
    # Day must be between 0 and 3 (Monday to Thursday)
    opt.add(day_var >= 0, day_var <= 3)
    # Start time must allow a 30-minute meeting within 9:00-17:00 (0 to 450 minutes)
    opt.add(start_var >= 0, start_var <= 450)
    
    # Add constraints for Mary's busy intervals
    for day, intervals in mary_busy.items():
        for s, e in intervals:
            # Meeting must not overlap: either ends before busy starts or starts after busy ends
            opt.add(Implies(day_var == day, Or(start_var + 30 <= s, start_var >= e)))
    
    # Add constraints for Alexis's busy intervals
    for day, intervals in alexis_busy.items():
        for s, e in intervals:
            opt.add(Implies(day_var == day, Or(start_var + 30 <= s, start_var >= e)))
    
    # Minimize: earlier day and then earlier start time
    cost = day_var * 10000 + start_var
    opt.minimize(cost)
    
    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        d = model[day_var].as_long()
        s = model[start_var].as_long()
        
        day_str = days[d]
        total_minutes_start = s
        start_hour = 9 + total_minutes_start // 60
        start_minute = total_minutes_start % 60
        end_minutes = total_minutes_start + 30
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()