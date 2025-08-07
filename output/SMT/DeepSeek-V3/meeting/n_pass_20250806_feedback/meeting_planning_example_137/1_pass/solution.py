from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Convert times to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Base time is 9:00 AM (540 minutes)
    base_time = 540

    # Define variables for meeting start and end times in minutes since base_time
    meet_barbara_start = Int('meet_barbara_start')
    meet_barbara_end = Int('meet_barbara_end')
    meet_kenneth_start = Int('meet_kenneth_start')
    meet_kenneth_end = Int('meet_kenneth_end')

    # Barbara's availability: 8:15 AM (495) to 7:00 PM (1140)
    barbara_start_available = 495  # 8:15 AM
    barbara_end_available = 1140   # 7:00 PM

    # Kenneth's availability: 12:00 PM (720) to 3:00 PM (900)
    kenneth_start_available = 720  # 12:00 PM
    kenneth_end_available = 900    # 3:00 PM

    # Travel times in minutes
    fd_to_chinatown = 5
    fd_to_golden_gate = 23
    chinatown_to_golden_gate = 23
    golden_gate_to_chinatown = 23
    golden_gate_to_fd = 26
    chinatown_to_fd = 5

    # Constraints for Barbara's meeting
    s.add(meet_barbara_start >= barbara_start_available)
    s.add(meet_barbara_end <= barbara_end_available)
    s.add(meet_barbara_end - meet_barbara_start >= 45)  # at least 45 minutes

    # Constraints for Kenneth's meeting
    s.add(meet_kenneth_start >= kenneth_start_available)
    s.add(meet_kenneth_end <= kenneth_end_available)
    s.add(meet_kenneth_end - meet_kenneth_start >= 90)  # at least 90 minutes

    # Initial location: Financial District at 9:00 AM (540)
    # We need to model the sequence of meetings and travels

    # There are two possible orders:
    # 1. Meet Barbara first, then Kenneth
    # 2. Meet Kenneth first, then Barbara

    # We'll create two separate scenarios and choose the feasible one

    # Scenario 1: Meet Barbara first, then Kenneth
    scenario1 = Solver()
    scenario1.add(meet_barbara_start >= base_time + fd_to_golden_gate)  # travel to Golden Gate
    scenario1.add(meet_kenneth_start >= meet_barbara_end + golden_gate_to_chinatown)  # travel to Chinatown
    scenario1.add(meet_barbara_start >= barbara_start_available)
    scenario1.add(meet_barbara_end <= barbara_end_available)
    scenario1.add(meet_barbara_end - meet_barbara_start >= 45)
    scenario1.add(meet_kenneth_start >= kenneth_start_available)
    scenario1.add(meet_kenneth_end <= kenneth_end_available)
    scenario1.add(meet_kenneth_end - meet_kenneth_start >= 90)

    # Scenario 2: Meet Kenneth first, then Barbara
    scenario2 = Solver()
    scenario2.add(meet_kenneth_start >= base_time + fd_to_chinatown)  # travel to Chinatown
    scenario2.add(meet_barbara_start >= meet_kenneth_end + chinatown_to_golden_gate)  # travel to Golden Gate
    scenario2.add(meet_barbara_start >= barbara_start_available)
    scenario2.add(meet_barbara_end <= barbara_end_available)
    scenario2.add(meet_barbara_end - meet_barbara_start >= 45)
    scenario2.add(meet_kenneth_start >= kenneth_start_available)
    scenario2.add(meet_kenneth_end <= kenneth_end_available)
    scenario2.add(meet_kenneth_end - meet_kenneth_start >= 90)

    itinerary = []

    # Check which scenario is feasible
    if scenario1.check() == sat:
        model = scenario1.model()
        barbara_start = model[meet_barbara_start].as_long()
        barbara_end = model[meet_barbara_end].as_long()
        kenneth_start = model[meet_kenneth_start].as_long()
        kenneth_end = model[meet_kenneth_end].as_long()

        itinerary = [
            {"action": "meet", "person": "Barbara", "start_time": minutes_to_time(barbara_start), "end_time": minutes_to_time(barbara_end)},
            {"action": "meet", "person": "Kenneth", "start_time": minutes_to_time(kenneth_start), "end_time": minutes_to_time(kenneth_end)}
        ]
    elif scenario2.check() == sat:
        model = scenario2.model()
        kenneth_start = model[meet_kenneth_start].as_long()
        kenneth_end = model[meet_kenneth_end].as_long()
        barbara_start = model[meet_barbara_start].as_long()
        barbara_end = model[meet_barbara_end].as_long()

        itinerary = [
            {"action": "meet", "person": "Kenneth", "start_time": minutes_to_time(kenneth_start), "end_time": minutes_to_time(kenneth_end)},
            {"action": "meet", "person": "Barbara", "start_time": minutes_to_time(barbara_start), "end_time": minutes_to_time(barbara_end)}
        ]
    else:
        # No feasible schedule found
        return {"itinerary": []}

    return {"itinerary": itinerary}

# Execute the solver
result = solve_scheduling()
print(result)