from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    # Convert all times to minutes from 9:00 AM (540 minutes since midnight)
    
    # Melissa's meeting at North Beach: 8:15 AM to 1:30 PM (495 to 810 minutes from midnight)
    # Since we arrive at Sunset at 9:00 AM (540), we can't meet Melissa before 9:00 AM.
    melissa_start = Int('melissa_start')  # minutes from 9:00 AM
    melissa_end = Int('melissa_end')
    
    # Anthony's meeting at Chinatown: 1:15 PM to 2:30 PM (795 to 870 minutes from midnight)
    anthony_start = Int('anthony_start')  # minutes from 9:00 AM
    anthony_end = Int('anthony_end')
    
    # Rebecca's meeting at Russian Hill: 7:30 PM to 9:15 PM (1110 to 1230 minutes from midnight)
    rebecca_start = Int('rebecca_start')  # minutes from 9:00 AM
    rebecca_end = Int('rebecca_end')
    
    # Convert friend availability windows to minutes from 9:00 AM
    melissa_window_start = 0  # 9:00 AM is 0 minutes from 9:00 AM
    melissa_window_end = 270  # 1:30 PM is 270 minutes from 9:00 AM
    
    anthony_window_start = 255  # 1:15 PM is 255 minutes from 9:00 AM
    anthony_window_end = 330    # 2:30 PM is 330 minutes from 9:00 AM
    
    rebecca_window_start = 570  # 7:30 PM is 570 minutes from 9:00 AM
    rebecca_window_end = 690    # 9:15 PM is 690 minutes from 9:00 AM
    
    # Meeting duration constraints
    s.add(melissa_end == melissa_start + 105)  # Melissa: 105 minutes
    s.add(anthony_end == anthony_start + 60)   # Anthony: 60 minutes
    s.add(rebecca_end == rebecca_start + 105)  # Rebecca: 105 minutes
    
    # Meeting must be within their availability windows
    s.add(melissa_start >= melissa_window_start)
    s.add(melissa_end <= melissa_window_end)
    
    s.add(anthony_start >= anthony_window_start)
    s.add(anthony_end <= anthony_window_end)
    
    s.add(rebecca_start >= rebecca_window_start)
    s.add(rebecca_end <= rebecca_window_end)
    
    # Travel times between locations
    # Start at Sunset at 0 minutes (9:00 AM), travel to North Beach to meet Melissa: 29 minutes
    s.add(melissa_start >= 29)
    
    # Travel from North Beach to Chinatown: 6 minutes
    s.add(anthony_start >= melissa_end + 6)
    
    # Travel from Chinatown to Russian Hill: 7 minutes
    s.add(rebecca_start >= anthony_end + 7)
    
    # Ensure Rebecca's meeting starts no earlier than 7:30 PM (570 minutes from 9:00 AM)
    s.add(rebecca_start >= 570)
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        
        # Get the meeting times in minutes from 9:00 AM
        melissa_s = m.eval(melissa_start).as_long()
        anthony_s = m.eval(anthony_start).as_long()
        rebecca_s = m.eval(rebecca_start).as_long()
        
        melissa_e = m.eval(melissa_end).as_long()
        anthony_e = m.eval(anthony_end).as_long()
        rebecca_e = m.eval(rebecca_end).as_long()
        
        # Convert minutes from 9:00 AM back to HH:MM format
        def to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"
        
        itinerary = [
            {"action": "meet", "person": "Melissa", "start_time": to_time(melissa_s), "end_time": to_time(melissa_e)},
            {"action": "meet", "person": "Anthony", "start_time": to_time(anthony_s), "end_time": to_time(anthony_e)},
            {"action": "meet", "person": "Rebecca", "start_time": to_time(rebecca_s), "end_time": to_time(rebecca_e)}
        ]
        
        return {"itinerary": itinerary}
    else:
        # Try alternative sequences if the first one doesn't work
        # For this problem, sequence 1 should work
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))