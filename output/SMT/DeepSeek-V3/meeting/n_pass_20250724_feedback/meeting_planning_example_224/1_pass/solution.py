from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    # Melissa at Golden Gate Park
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')
    
    # Nancy at Presidio
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')
    
    # Emily at Richmond District
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')

    # Convert all times to minutes since 9:00 AM (540 minutes in 24-hour format)
    # Melissa available from 8:30 AM (510) to 8:00 PM (1200)
    s.add(melissa_start >= 510 - 540)  # 9:00 AM is 0, so 8:30 AM is -30
    s.add(melissa_end <= 1200 - 540)   # 8:00 PM is 1200, so 1200 - 540 = 660
    s.add(melissa_end - melissa_start >= 15)
    
    # Nancy available from 7:45 PM (1140) to 10:00 PM (1320)
    s.add(nancy_start >= 1140 - 540)   # 1140 - 540 = 600
    s.add(nancy_end <= 1320 - 540)     # 1320 - 540 = 780
    s.add(nancy_end - nancy_start >= 105)
    
    # Emily available from 4:45 PM (990) to 10:00 PM (1320)
    s.add(emily_start >= 990 - 540)    # 990 - 540 = 450
    s.add(emily_end <= 1320 - 540)     # 1320 - 540 = 780
    s.add(emily_end - emily_start >= 120)
    
    # All start times must be >= 0 (since we start at 9:00 AM)
    s.add(melissa_start >= 0)
    s.add(nancy_start >= 0)
    s.add(emily_start >= 0)

    # Define the order of meetings and travel times
    # We need to decide the order of meetings: Melissa, Emily, Nancy
    # Possible orders: Melissa -> Emily -> Nancy or Emily -> Melissa -> Nancy, etc.
    # But meeting Nancy must be after 7:45 PM (600 in our time), and Emily's meeting is long.
    # Let's assume the order is Melissa -> Emily -> Nancy.

    # Travel from Fisherman's Wharf to Golden Gate Park: 25 minutes
    s.add(melissa_start >= 25)  # leave at 9:00, arrive at 9:25
    
    # Travel from Golden Gate Park to Richmond District: 7 minutes
    s.add(emily_start >= melissa_end + 7)
    
    # Travel from Richmond District to Presidio: 7 minutes
    s.add(nancy_start >= emily_end + 7)

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        melissa_s = m.eval(melissa_start).as_long()
        melissa_e = m.eval(melissa_end).as_long()
        emily_s = m.eval(emily_start).as_long()
        emily_e = m.eval(emily_end).as_long()
        nancy_s = m.eval(nancy_start).as_long()
        nancy_e = m.eval(nancy_end).as_long()
        
        itinerary = [
            {"action": "meet", "person": "Melissa", "start_time": minutes_to_time(melissa_s), "end_time": minutes_to_time(melissa_e)},
            {"action": "meet", "person": "Emily", "start_time": minutes_to_time(emily_s), "end_time": minutes_to_time(emily_e)},
            {"action": "meet", "person": "Nancy", "start_time": minutes_to_time(nancy_s), "end_time": minutes_to_time(nancy_e)}
        ]
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))