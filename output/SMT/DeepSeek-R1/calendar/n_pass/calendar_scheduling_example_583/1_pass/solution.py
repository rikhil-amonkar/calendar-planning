from z3 import *

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    total_minutes = (hours - 9) * 60 + minutes
    return total_minutes

def main():
    # Busy periods for Lisa and Anthony in minutes (from 9:00)
    lisa_busy = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("14:00"), time_to_minutes("16:00"))
    ]
    
    anthony_busy = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    s = Optimize()
    start = Int('start')
    
    # Meeting must be within 9:00 to 17:00 (0 to 480 minutes)
    s.add(start >= 0)
    s.add(start <= 450)  # 450 because meeting lasts 30 minutes (450+30=480)
    
    # Function to add non-overlap constraints for a set of busy periods
    def add_busy_constraints(busy_periods):
        for s_start, s_end in busy_periods:
            # Meeting is either before or after the busy period
            s.add(Or(start >= s_end, start + 30 <= s_start))
    
    add_busy_constraints(lisa_busy)
    add_busy_constraints(anthony_busy)
    
    s.minimize(start)
    
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        # Convert start_val back to time string
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        end_minutes = start_val + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()