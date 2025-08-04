from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define variables for meeting start and end times
    # Meet Barbara at Golden Gate Park
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')

    # Meet Kenneth at Chinatown
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    start_time = 540  # 9:00 AM in minutes

    # Barbara's availability: 8:15 AM (495) to 7:00 PM (1140)
    barbara_available_start = 495
    barbara_available_end = 1140

    # Kenneth's availability: 12:00 PM (720) to 3:00 PM (900)
    kenneth_available_start = 720
    kenneth_available_end = 900

    # Travel times in minutes
    fd_to_chinatown = 5
    fd_to_golden_gate = 23
    chinatown_to_golden_gate = 23
    golden_gate_to_chinatown = 23
    chinatown_to_fd = 5
    golden_gate_to_fd = 26

    # Constraints for Barbara
    opt.add(barbara_start >= barbara_available_start)
    opt.add(barbara_end <= barbara_available_end)
    opt.add(barbara_end - barbara_start >= 45)  # At least 45 minutes with Barbara

    # Constraints for Kenneth
    opt.add(kenneth_start >= kenneth_available_start)
    opt.add(kenneth_end <= kenneth_available_end)
    opt.add(kenneth_end - kenneth_start >= 90)  # At least 90 minutes with Kenneth

    # Possible schedules:
    # Option 1: Financial District -> Golden Gate Park -> Chinatown
    # Option 2: Financial District -> Chinatown -> Golden Gate Park
    # We'll let Z3 choose the best order

    # Define order variables
    meet_barbara_first = Bool('meet_barbara_first')

    # If meeting Barbara first:
    opt.add(Implies(meet_barbara_first, barbara_start >= start_time + fd_to_golden_gate))
    opt.add(Implies(meet_barbara_first, kenneth_start >= barbara_end + golden_gate_to_chinatown))

    # If meeting Kenneth first:
    opt.add(Implies(Not(meet_barbara_first), kenneth_start >= start_time + fd_to_chinatown))
    opt.add(Implies(Not(meet_barbara_first), barbara_start >= kenneth_end + chinatown_to_golden_gate))

    # Ensure no overlap and valid travel times
    opt.add(barbara_end <= barbara_available_end)
    opt.add(kenneth_end <= kenneth_available_end)

    # Maximize total meeting time
    total_meeting_time = (barbara_end - barbara_start) + (kenneth_end - kenneth_start)
    opt.maximize(total_meeting_time)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        barbara_start_val = m.evaluate(barbara_start).as_long()
        barbara_end_val = m.evaluate(barbara_end).as_long()
        kenneth_start_val = m.evaluate(kenneth_start).as_long()
        kenneth_end_val = m.evaluate(kenneth_end).as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        itinerary = [
            {"action": "meet", "person": "Barbara", "start_time": minutes_to_time(barbara_start_val), "end_time": minutes_to_time(barbara_end_val)},
            {"action": "meet", "person": "Kenneth", "start_time": minutes_to_time(kenneth_start_val), "end_time": minutes_to_time(kenneth_end_val)}
        ]

        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))