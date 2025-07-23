from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Convert all times to minutes since 9:00 AM (0 = 9:00 AM)
    # Timothy's availability: 8:45 PM to 9:30 PM
    timothy_start = (12 * 60 + 45) - (9 * 60)  # 11*60 + 45 = 705 minutes
    timothy_end = (12 * 60 + 30) - (9 * 60)    # 12*60 + 30 = 750 minutes
    
    # Travel times (minutes)
    to_richmond = 12
    from_richmond = 13
    
    # Decision variables
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')
    
    # Constraints:
    # 1. Meeting must be within Timothy's availability
    s.add(meet_start >= timothy_start)
    s.add(meet_end <= timothy_end)
    
    # 2. Meeting duration must be exactly 45 minutes
    s.add(meet_end - meet_start == 45)
    
    # 3. Travel constraints
    departure_time = meet_start - to_richmond
    return_time = meet_end + from_richmond
    
    # 4. Can't leave before 9:00 AM (0 minutes)
    s.add(departure_time >= 0)
    
    # 5. Only one meeting (implicit by only scheduling Timothy)
    
    if s.check() == sat:
        m = s.model()
        # Convert times back to readable format
        def format_time(minutes):
            hours = (minutes // 60) + 9
            mins = minutes % 60
            ampm = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{mins:02d} {ampm}"
        
        print("Feasible schedule found:")
        print(f"- Depart Alamo Square at: {format_time(m[departure_time].as_long())}")
        print(f"- Meet Timothy from: {format_time(m[meet_start].as_long())} to {format_time(m[meet_end].as_long())}")
        print(f"- Return to Alamo Square at: {format_time(m[return_time].as_long())}")
    else:
        print("No feasible schedule found that meets all constraints.")

solve_scheduling()