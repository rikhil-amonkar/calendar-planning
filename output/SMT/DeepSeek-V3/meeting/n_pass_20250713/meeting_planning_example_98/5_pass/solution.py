from z3 import *

def solve_scheduling():
    s = Solver()
    
    # Convert all times to minutes since 9:00 AM (0 = 9:00 AM)
    # Timothy's availability: 8:45 PM to 9:30 PM (11h45m to 12h30m after 9AM)
    timothy_start = 11*60 + 45  # 705 minutes
    timothy_end = 12*60 + 30    # 750 minutes
    
    # Travel times (minutes)
    to_richmond = 12
    from_richmond = 13
    
    # Meeting variables
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')
    
    # Constraints:
    # 1. Meeting must be within Timothy's availability
    s.add(meet_start >= timothy_start)
    s.add(meet_end <= timothy_end)
    
    # 2. Meeting duration must be exactly 45 minutes
    s.add(meet_end - meet_start == 45)
    
    # 3. Travel time constraints
    departure_time = meet_start - to_richmond
    return_time = meet_end + from_richmond
    
    # 4. Can't leave before 9:00 AM (0 minutes)
    s.add(departure_time >= 0)
    
    # 5. Only one meeting (implicit by only scheduling Timothy)
    
    if s.check() == sat:
        m = s.model()
        # Convert minutes to readable time format
        def format_time(mins):
            total_mins = mins
            hours = (total_mins // 60) + 9
            minutes = total_mins % 60
            period = "PM" if hours >= 12 else "AM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{minutes:02d} {period}"
        
        print("Valid schedule found:")
        print(f"1. Depart Alamo Square at: {format_time(m[departure_time].as_long())}")
        print(f"2. Meet Timothy from: {format_time(m[meet_start].as_long())} to {format_time(m[meet_end].as_long())}")
        print(f"3. Return to Alamo Square at: {format_time(m[return_time].as_long())}")
        print("\nThis schedule meets exactly one person (Timothy) for exactly 45 minutes.")
    else:
        print("No valid schedule found that meets all constraints.")

solve_scheduling()