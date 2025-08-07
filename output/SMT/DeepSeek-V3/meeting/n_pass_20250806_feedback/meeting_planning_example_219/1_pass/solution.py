from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Emily at Alamo Square
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    
    # Meeting with Barbara at Union Square
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    
    # Meeting with William at Chinatown
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Emily's window: 11:45 AM (705) to 3:15 PM (915)
    emily_window_start = 705
    emily_window_end = 915
    
    # Barbara's window: 4:45 PM (1005) to 6:15 PM (1095)
    barbara_window_start = 1005
    barbara_window_end = 1095
    
    # William's window: 5:15 PM (1035) to 7:00 PM (1140)
    william_window_start = 1035
    william_window_end = 1140

    # Travel times from The Castro (starting point)
    # The Castro to Alamo Square: 8 minutes
    travel_castro_to_alamo = 8
    
    # The Castro to Union Square: 19
    travel_castro_to_union = 19
    
    # The Castro to Chinatown: 20
    travel_castro_to_china = 20

    # Travel times between other locations
    # Alamo to Union: 14
    travel_alamo_to_union = 14
    
    # Alamo to Chinatown: 16
    travel_alamo_to_china = 16
    
    # Union to Chinatown: 7
    travel_union_to_china = 7
    
    # Chinatown to Union: 7
    travel_china_to_union = 7

    # Constraints for Emily's meeting
    s.add(emily_start >= emily_window_start)
    s.add(emily_end <= emily_window_end)
    s.add(emily_end - emily_start >= 105)  # 105 minutes minimum
    
    # Constraints for Barbara's meeting
    s.add(barbara_start >= barbara_window_start)
    s.add(barbara_end <= barbara_window_end)
    s.add(barbara_end - barbara_start >= 60)  # 60 minutes minimum
    
    # Constraints for William's meeting
    s.add(william_start >= william_window_start)
    s.add(william_end <= william_window_end)
    s.add(william_end - william_start >= 105)  # 105 minutes minimum

    # Starting at The Castro at 9:00 AM (540 minutes)
    # Possible sequences:
    # Option 1: Emily -> Barbara -> William
    # Option 2: Emily -> William -> Barbara
    # (Other sequences may not fit due to time constraints)
    
    # We'll model both options and see which one is feasible
    
    # Option 1: Emily -> Barbara -> William
    option1 = And(
        emily_start >= 540 + travel_castro_to_alamo,  # Travel to Alamo Square first
        barbara_start >= emily_end + travel_alamo_to_union,
        william_start >= barbara_end + travel_union_to_china
    )
    
    # Option 2: Emily -> William -> Barbara
    option2 = And(
        emily_start >= 540 + travel_castro_to_alamo,
        william_start >= emily_end + travel_alamo_to_china,
        barbara_start >= william_end + travel_china_to_union
    )
    
    # Add either option1 or option2
    s.add(Or(option1, option2))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        
        # Extract the meeting times
        emily_s = model[emily_start].as_long()
        emily_e = model[emily_end].as_long()
        barbara_s = model[barbara_start].as_long()
        barbara_e = model[barbara_end].as_long()
        william_s = model[william_start].as_long()
        william_e = model[william_end].as_long()
        
        # Convert minutes back to HH:MM format
        def minutes_to_time(m):
            hours = m // 60
            minutes = m % 60
            return f"{hours:02d}:{minutes:02d}"
        
        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": minutes_to_time(emily_s), "end_time": minutes_to_time(emily_e)},
            {"action": "meet", "person": "Barbara", "start_time": minutes_to_time(barbara_s), "end_time": minutes_to_time(barbara_e)},
            {"action": "meet", "person": "William", "start_time": minutes_to_time(william_s), "end_time": minutes_to_time(william_e)}
        ]
        
        # Determine the order based on start times
        # Sort the itinerary by start time
        itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
        
        return {"itinerary": itinerary_sorted}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))