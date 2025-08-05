from z3 import *

def main():
    # Days indexed: 0=Monday, 1=Tuesday, 2=Wednesday
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Busy intervals in minutes from 9:00 for each day and participant
    days_busy = {
        0: {'Nancy': [(60, 90), (150, 210), (270, 300), (330, 390), (420, 480)],
            'Jose': [(0, 480)]},
        1: {'Nancy': [(30, 90), (120, 150), (180, 210), (240, 270), (390, 420)],
            'Jose': [(0, 480)]},
        2: {'Nancy': [(60, 150), (270, 420)],
            'Jose': [(0, 30), (60, 210), (270, 330), (360, 480)]}
    }
    
    # Create Z3 variables
    day_index = Int('day_index')
    start_minute = Int('start_minute')
    
    # Create optimizer
    o = Optimize()
    
    # Constraints: day_index must be 0, 1, or 2; start_minute between 0 and 450 inclusive
    o.add(day_index >= 0, day_index <= 2)
    o.add(start_minute >= 0, start_minute <= 450)
    
    # For each day, add constraints that the meeting avoids all busy intervals of both participants
    for d in [0, 1, 2]:
        cond_list = []
        for participant in ['Nancy', 'Jose']:
            for interval in days_busy[d][participant]:
                busystart, busyend = interval
                # Meeting must be entirely before or after the busy interval
                cond_list.append(Or(start_minute + 30 <= busystart, start_minute >= busyend))
        # If meeting is on day `d`, then all conditions must hold
        o.add(Implies(day_index == d, And(cond_list)))
    
    # Minimize total minutes from Monday 9:00
    total_minutes = day_index * 480 + start_minute
    o.minimize(total_minutes)
    
    # Check for a solution
    if o.check() == sat:
        m = o.model()
        d_val = m[day_index].as_long()
        s_val = m[start_minute].as_long()
        
        day_str = days[d_val]
        base_hour = 9
        total_minutes_from_9 = s_val
        hours = total_minutes_from_9 // 60
        minutes = total_minutes_from_9 % 60
        start_hour = base_hour + hours
        start_minute_val = minutes
        start_time_str = f"{start_hour:02d}:{minutes:02d}"
        
        end_minute_total = total_minutes_from_9 + 30
        end_hour = base_hour + end_minute_total // 60
        end_minute_val = end_minute_total % 60
        end_time_str = f"{end_hour:02d}:{end_minute_val:02d}"
        
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()