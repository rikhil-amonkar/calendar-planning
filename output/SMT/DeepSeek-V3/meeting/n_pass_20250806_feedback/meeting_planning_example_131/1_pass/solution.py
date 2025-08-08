from z3 import *

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Jason at Presidio
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    
    # Meeting with Kenneth at Marina District
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')
    
    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Jason's availability: 10:00 AM (600) to 4:15 PM (975)
    jason_available_start = 600
    jason_available_end = 975
    
    # Kenneth's availability: 3:30 PM (930) to 4:45 PM (1005)
    kenneth_available_start = 930
    kenneth_available_end = 1005
    
    # Travel times from Pacific Heights to Presidio: 11 minutes
    # Initial location: Pacific Heights at 540 (9:00 AM)
    
    # Constraints for Jason's meeting
    s.add(jason_start >= jason_available_start)
    s.add(jason_end <= jason_available_end)
    s.add(jason_end - jason_start >= 90)  # at least 90 minutes
    
    # Constraints for Kenneth's meeting
    s.add(kenneth_start >= kenneth_available_start)
    s.add(kenneth_end <= kenneth_available_end)
    s.add(kenneth_end - kenneth_start >= 45)  # at least 45 minutes
    
    # Travel constraints
    # From Pacific Heights to Presidio: 11 minutes
    # So Jason's meeting can start earliest at 540 + 11 = 551 (9:11 AM), but Jason is available only from 10:00 AM
    # So no issue here.
    
    # From Presidio to Marina District: 10 minutes
    # So after meeting Jason, travel to Marina takes 10 minutes
    # So kenneth_start >= jason_end + 10
    s.add(kenneth_start >= jason_end + 10)
    
    # Also, check if the schedule is feasible (Kenneth's meeting must start after Jason's meeting ends plus travel time)
    # Ensure that the Kenneth meeting can fit after Jason's meeting
    
    # Check if the solution is feasible
    if s.check() == sat:
        m = s.model()
        # Extract times
        js = m.evaluate(jason_start).as_long()
        je = m.evaluate(jason_end).as_long()
        ks = m.evaluate(kenneth_start).as_long()
        ke = m.evaluate(kenneth_end).as_long()
        
        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"
        
        itinerary = [
            {"action": "meet", "person": "Jason", "start_time": minutes_to_time(js), "end_time": minutes_to_time(je)},
            {"action": "meet", "person": "Kenneth", "start_time": minutes_to_time(ks), "end_time": minutes_to_time(ke)}
        ]
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
solution = solve_scheduling_problem()
print(solution)