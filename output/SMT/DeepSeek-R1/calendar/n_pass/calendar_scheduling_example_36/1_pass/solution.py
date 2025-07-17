from z3 import *

def main():
    s = Int('s')
    opt = Optimize()
    
    # Work hours: 9:00 to 17:00 -> meeting must start by 16:00 (420 minutes from 9:00)
    opt.add(s >= 0)
    opt.add(s <= 420)  # because 420 + 60 = 480 (17:00)
    
    # Ryan's busy: 9:00-9:30 (0 to 30) and 12:30-13:00 (210 to 240)
    # For [0,30]: meeting must not overlap -> s >= 30
    opt.add(s >= 30)
    # For [210,240]: meeting must end by 210 or start at/after 240. 
    # But since we have Denise's constraint (meeting ends by 210), we ensure meeting ends by 210 (s+60 <= 210) which is covered later.
    
    # Denise's constraints:
    # Busy: 9:30-10:30 (30 to 90) -> meeting must start at or after 90
    opt.add(s >= 90)
    # Busy: 12:00-13:00 (180 to 240) -> meeting must end by 180 or start at/after 240. 
    # Since meeting ends by 210 (s+60 <= 210) and s>=90, we require s+60 <= 180 -> s <= 120
    opt.add(s <= 120)
    # Additional constraint: Denise does not want to meet after 12:30 (210 minutes) -> meeting must end by 210
    opt.add(s + 60 <= 210)
    
    # Minimize start time to get the earliest slot
    opt.minimize(s)
    
    if opt.check() == sat:
        m = opt.model()
        start_minutes = m[s].as_long()
        
        # Calculate start time in HH:MM
        total_minutes_from_9 = start_minutes
        hours = total_minutes_from_9 // 60
        minutes = total_minutes_from_9 % 60
        start_hour = 9 + hours
        start_minute = minutes
        
        # Calculate end time
        end_minutes = start_minutes + 60
        end_hours = end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_hour = 9 + end_hours
        end_minute = end_minutes_remainder
        
        # Format to two-digit strings
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()