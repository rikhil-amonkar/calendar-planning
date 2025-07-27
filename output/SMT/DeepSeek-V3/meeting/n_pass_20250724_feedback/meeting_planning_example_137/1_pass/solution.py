from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for meeting start and end times
    # Barbara's meeting at Golden Gate Park
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    
    # Kenneth's meeting at Chinatown
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')
    
    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    start_of_day = 540  # 9:00 AM in minutes
    
    # Barbara's availability: 8:15 AM (495) to 7:00 PM (1140)
    barbara_available_start = 495
    barbara_available_end = 1140
    
    # Kenneth's availability: 12:00 PM (720) to 3:00 PM (900)
    kenneth_available_start = 720
    kenneth_available_end = 900
    
    # Minimum meeting durations
    barbara_min_duration = 45
    kenneth_min_duration = 90
    
    # Travel times in minutes
    fd_to_chinatown = 5
    fd_to_golden_gate = 23
    chinatown_to_golden_gate = 23
    golden_gate_to_chinatown = 23
    golden_gate_to_fd = 26
    chinatown_to_fd = 5
    
    # Constraints for Barbara's meeting
    s.add(barbara_start >= barbara_available_start)
    s.add(barbara_end <= barbara_available_end)
    s.add(barbara_end >= barbara_start + barbara_min_duration)
    
    # Constraints for Kenneth's meeting
    s.add(kenneth_start >= kenneth_available_start)
    s.add(kenneth_end <= kenneth_available_end)
    s.add(kenneth_end >= kenneth_start + kenneth_min_duration)
    
    # We start at Financial District at 9:00 AM (540)
    # There are two possible orders: meet Barbara first or Kenneth first
    
    # Option 1: Meet Barbara first, then Kenneth
    # Travel from FD to Golden Gate Park: 23 minutes
    # Then travel from Golden Gate Park to Chinatown: 23 minutes
    option1 = And(
        barbara_start >= start_of_day + fd_to_golden_gate,
        kenneth_start >= barbara_end + golden_gate_to_chinatown
    )
    
    # Option 2: Meet Kenneth first, then Barbara
    # Travel from FD to Chinatown: 5 minutes
    # Then travel from Chinatown to Golden Gate Park: 23 minutes
    option2 = And(
        kenneth_start >= start_of_day + fd_to_chinatown,
        barbara_start >= kenneth_end + chinatown_to_golden_gate
    )
    
    # We need to choose one of the options
    s.add(Or(option1, option2))
    
    # We want to maximize the number of friends met (both in this case)
    # So no additional constraints needed
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        
        # Extract the meeting times
        barbara_start_time = m[barbara_start].as_long()
        barbara_end_time = m[barbara_end].as_long()
        kenneth_start_time = m[kenneth_start].as_long()
        kenneth_end_time = m[kenneth_end].as_long()
        
        # Convert minutes to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        itinerary = []
        
        # Determine the order of meetings based on which option was chosen
        if m.evaluate(option1):
            # Barbara first
            itinerary.append({
                "action": "meet",
                "person": "Barbara",
                "start_time": minutes_to_time(barbara_start_time),
                "end_time": minutes_to_time(barbara_end_time)
            })
            itinerary.append({
                "action": "meet",
                "person": "Kenneth",
                "start_time": minutes_to_time(kenneth_start_time),
                "end_time": minutes_to_time(kenneth_end_time)
            })
        else:
            # Kenneth first
            itinerary.append({
                "action": "meet",
                "person": "Kenneth",
                "start_time": minutes_to_time(kenneth_start_time),
                "end_time": minutes_to_time(kenneth_end_time)
            })
            itinerary.append({
                "action": "meet",
                "person": "Barbara",
                "start_time": minutes_to_time(barbara_start_time),
                "end_time": minutes_to_time(barbara_end_time)
            })
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve and print the result
result = solve_scheduling()
print(result)