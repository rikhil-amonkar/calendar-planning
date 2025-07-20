from z3 import *

def main():
    # Convert time string to minutes from 9:00
    def time_to_minutes(time_str):
        h, m = time_str.split(':')
        return (int(h) - 9) * 60 + int(m)
    
    # Busy intervals for Mary: day index 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    mary_busy = {
        0: [],  # Monday
        1: [(time_to_minutes("10:00"), time_to_minutes("10:30")), 
            (time_to_minutes("15:30"), time_to_minutes("16:00"))],  # Tuesday
        2: [(time_to_minutes("9:30"), time_to_minutes("10:00")), 
            (time_to_minutes("15:00"), time_to_minutes("15:30"))],  # Wednesday
        3: [(time_to_minutes("9:00"), time_to_minutes("10:00")), 
            (time_to_minutes("10:30"), time_to_minutes("11:30"))]   # Thursday
    }
    
    # Busy intervals for Alexis
    alexis_busy = {
        0: [(time_to_minutes("9:00"), time_to_minutes("10:00")),
            (time_to_minutes("10:30"), time_to_minutes("12:00")),
            (time_to_minutes("12:30"), time_to_minutes("16:30"))],  # Monday
        1: [(time_to_minutes("9:00"), time_to_minutes("10:00")),
            (time_to_minutes("10:30"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("17:00"))],  # Tuesday
        2: [(time_to_minutes("9:00"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("17:00"))],  # Wednesday
        3: [(time_to_minutes("10:00"), time_to_minutes("12:00")),
            (time_to_minutes("14:00"), time_to_minutes("14:30")),
            (time_to_minutes("15:30"), time_to_minutes("16:00")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))]  # Thursday
    }
    
    # Z3 variables
    day = Int('day')
    start = Int('start')
    
    # Solver with optimization
    opt = Optimize()
    
    # Constraints: day between 0-3, start between 0-450 (meeting ends at start+30 <= 480)
    opt.add(day >= 0)
    opt.add(day <= 3)
    opt.add(start >= 0)
    opt.add(start <= 450)
    
    # Non-overlap constraints per day
    for d in range(4):
        mary_cond = True
        for interval in mary_busy[d]:
            s, e = interval
            mary_cond = And(mary_cond, Or(start + 30 <= s, start >= e))
        
        alexis_cond = True
        for interval in alexis_busy[d]:
            s, e = interval
            alexis_cond = And(alexis_cond, Or(start + 30 <= s, start >= e))
        
        opt.add(If(day == d, And(mary_cond, alexis_cond), True))
    
    # Objective: minimize day and then start time
    objective = day * 10000 + start
    opt.minimize(objective)
    
    # Check and get the solution
    if opt.check() == sat:
        m = opt.model()
        sol_day = m[day].as_long()
        sol_start_minutes = m[start].as_long()
        
        # Convert day index to string
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_str = days[sol_day]
        
        # Convert start minutes to HH:MM format
        total_minutes = 9 * 60 + sol_start_minutes
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        # End time is start time + 30 minutes
        end_minutes = total_minutes + 30
        end_hours = end_minutes // 60
        end_minutes %= 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()