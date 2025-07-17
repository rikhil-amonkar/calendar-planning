from z3 import *

def main():
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Nicole's busy times in minutes from 9:00 (each interval is [start, end))
    nicole_busy = {
        'Tuesday': [(420, 450)],
        'Wednesday': [(360, 390)],
        'Friday': [(180, 210), (390, 420)]
    }
    
    # Daniel's busy times in minutes from 9:00 (each interval is [start, end))
    daniel_busy = {
        'Monday': [(0, 210), (240, 270), (300, 450)],
        'Tuesday': [(0, 90), (150, 210), (240, 270), (360, 420), (450, 480)],
        'Wednesday': [(0, 60), (120, 210), (240, 270), (300, 330), (450, 480)],
        'Thursday': [(120, 180), (240, 300), (360, 390)],
        'Friday': [(60, 120), (150, 180), (210, 330), (360, 390), (420, 450)]
    }
    
    # Initialize Z3 variables
    day_var = Int('day')
    start_var = Int('start')  # in minutes from 9:00
    
    # Initialize the optimizer
    opt = Optimize()
    
    # Day must be between 0 (Monday) and 4 (Friday)
    opt.add(day_var >= 0, day_var <= 4)
    # Start time must be between 0 and 420 minutes (so the meeting ends by 17:00)
    opt.add(start_var >= 0, start_var <= 420)
    
    # Add constraints for each day
    for i, day_name in enumerate(days):
        # For Nicole: if the meeting is on this day, it must avoid her busy intervals
        if day_name in nicole_busy:
            for interval in nicole_busy[day_name]:
                s, e = interval
                # Meeting [start, start+60] must not overlap [s, e)
                opt.add(Implies(day_var == i, Or(start_var + 60 <= s, start_var >= e)))
        
        # For Daniel: similarly avoid his busy intervals
        if day_name in daniel_busy:
            for interval in daniel_busy[day_name]:
                s, e = interval
                opt.add(Implies(day_var == i, Or(start_var + 60 <= s, start_var >= e)))
    
    # Define the total minutes from Monday 9:00 to minimize
    total_minutes = day_var * 480 + start_var
    opt.minimize(total_minutes)
    
    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        d_val = model[day_var].as_long()
        s_val = model[start_var].as_long()
        
        # Convert start time from minutes to HH:MM format
        start_hour = 9 + s_val // 60
        start_minute = s_val % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time (start time + 60 minutes)
        end_val = s_val + 60
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {days[d_val]}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()