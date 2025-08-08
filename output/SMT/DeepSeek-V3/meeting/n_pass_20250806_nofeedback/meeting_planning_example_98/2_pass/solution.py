from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()
    
    # Define variables for meeting start and end times (in minutes since midnight)
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')
    
    # Convert all times to minutes since midnight
    arrival_time = 9 * 60       # 09:00 (Alamo Square arrival)
    timothy_start = 20 * 60 + 45  # 20:45 (Timothy's availability start)
    timothy_end = 21 * 60 + 30    # 21:30 (Timothy's availability end)
    travel_time = 12              # Alamo Square to Richmond District
    
    # Constraints
    # 1. Meeting must be within Timothy's availability
    s.add(meet_start >= timothy_start)
    s.add(meet_end <= timothy_end)
    
    # 2. Meeting duration must be at least 45 minutes
    s.add(meet_end - meet_start >= 45)
    
    # 3. Must leave Alamo Square at meet_start - travel_time
    leave_time = meet_start - travel_time
    s.add(leave_time >= arrival_time)  # Can't leave before arriving
    
    # 4. The meeting must fit exactly in Timothy's window (since it's tight)
    s.add(meet_start == timothy_start)
    s.add(meet_end == timothy_end)
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        start = m[meet_start].as_long()
        end = m[meet_end].as_long()
        
        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        
        return {
            "itinerary": [
                {"action": "meet", "person": "Timothy", "start_time": start_time, "end_time": end_time}
            ]
        }
    else:
        return {"itinerary": []}

# Print the solution
solution = solve_scheduling()
print(solution)