from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define variables for meeting start and end times
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')

    # Convert all times to minutes since midnight
    start_time = 540  # 9:00 AM in minutes

    # Availability windows
    barbara_available_start = 495   # 8:15 AM
    barbara_available_end = 1140    # 7:00 PM
    kenneth_available_start = 720   # 12:00 PM
    kenneth_available_end = 900     # 3:00 PM

    # Travel times in minutes
    fd_to_chinatown = 5
    fd_to_golden_gate = 23
    chinatown_to_golden_gate = 23
    golden_gate_to_chinatown = 23

    # Meeting duration constraints
    min_barbara_time = 45
    min_kenneth_time = 90

    # Constraints for Barbara
    opt.add(barbara_start >= barbara_available_start)
    opt.add(barbara_end <= barbara_available_end)
    opt.add(barbara_end - barbara_start >= min_barbara_time)

    # Constraints for Kenneth
    opt.add(kenneth_start >= kenneth_available_start)
    opt.add(kenneth_end <= kenneth_available_end)
    opt.add(kenneth_end - kenneth_start >= min_kenneth_time)

    # Define two possible schedules
    # Option 1: Meet Barbara first, then Kenneth
    barbara_first = Bool('barbara_first')
    opt.add(Implies(barbara_first, barbara_start >= start_time + fd_to_golden_gate))
    opt.add(Implies(barbara_first, kenneth_start >= barbara_end + golden_gate_to_chinatown))

    # Option 2: Meet Kenneth first, then Barbara
    opt.add(Implies(Not(barbara_first), kenneth_start >= start_time + fd_to_chinatown))
    opt.add(Implies(Not(barbara_first), barbara_start >= kenneth_end + chinatown_to_golden_gate))

    # Maximize total meeting time
    total_meeting_time = (barbara_end - barbara_start) + (kenneth_end - kenneth_start)
    opt.maximize(total_meeting_time)

    if opt.check() == sat:
        m = opt.model()
        barbara_start_val = m.evaluate(barbara_start).as_long()
        barbara_end_val = m.evaluate(barbara_end).as_long()
        kenneth_start_val = m.evaluate(kenneth_start).as_long()
        kenneth_end_val = m.evaluate(kenneth_end).as_long()

        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        itinerary = []
        
        # Add meetings in chronological order
        if kenneth_start_val < barbara_start_val:
            itinerary.append({
                "action": "meet", 
                "person": "Kenneth", 
                "start_time": minutes_to_time(kenneth_start_val), 
                "end_time": minutes_to_time(kenneth_end_val)
            })
            itinerary.append({
                "action": "meet", 
                "person": "Barbara", 
                "start_time": minutes_to_time(barbara_start_val), 
                "end_time": minutes_to_time(barbara_end_val)
            })
        else:
            itinerary.append({
                "action": "meet", 
                "person": "Barbara", 
                "start_time": minutes_to_time(barbara_start_val), 
                "end_time": minutes_to_time(barbara_end_val)
            })
            itinerary.append({
                "action": "meet", 
                "person": "Kenneth", 
                "start_time": minutes_to_time(kenneth_start_val), 
                "end_time": minutes_to_time(kenneth_end_val)
            })

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))