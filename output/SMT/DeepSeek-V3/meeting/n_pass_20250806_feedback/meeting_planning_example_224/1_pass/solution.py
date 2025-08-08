from z3 import *
import datetime

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Melissa at Golden Gate Park
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')

    # Meeting with Nancy at Presidio
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')

    # Meeting with Emily at Richmond District
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    start_of_day = 540  # 9:00 AM in minutes (since midnight)

    # Melissa's availability: 8:30 AM (510) to 8:00 PM (1200)
    melissa_available_start = 510
    melissa_available_end = 1200

    # Nancy's availability: 7:45 PM (1185) to 10:00 PM (1320)
    nancy_available_start = 1185
    nancy_available_end = 1320

    # Emily's availability: 4:45 PM (1005) to 10:00 PM (1320)
    emily_available_start = 1005
    emily_available_end = 1320

    # Meeting duration constraints
    s.add(melissa_end == melissa_start + 15)  # Melissa: 15 minutes
    s.add(nancy_end == nancy_start + 105)    # Nancy: 105 minutes
    s.add(emily_end == emily_start + 120)    # Emily: 120 minutes

    # Meeting must be within friend's availability
    s.add(melissa_start >= melissa_available_start)
    s.add(melissa_end <= melissa_available_end)
    s.add(nancy_start >= nancy_available_start)
    s.add(nancy_end <= nancy_available_end)
    s.add(emily_start >= emily_available_start)
    s.add(emily_end <= emily_available_end)

    # Define travel times in minutes
    travel_fw_to_ggp = 25  # Fisherman's Wharf to Golden Gate Park
    travel_ggp_to_rd = 7   # Golden Gate Park to Richmond District
    travel_rd_to_presidio = 7  # Richmond District to Presidio

    # Possible schedules:
    # Option 1: Meet Melissa first, then Emily, then Nancy
    # Constraints for this option:
    # Start at Fisherman's Wharf at 9:00 AM (540)
    # Travel to Golden Gate Park: arrives at 540 + 25 = 565
    # Meet Melissa starts at >= 565 and ends by melissa_end
    # Then travel to Richmond District: time after melissa_end + 7
    # Meet Emily starts at >= melissa_end + 7
    # Then travel to Presidio: time after emily_end + 7
    # Meet Nancy starts at >= emily_end + 7

    # Add constraints for this schedule option
    s.add(melissa_start >= 540 + travel_fw_to_ggp)
    s.add(emily_start >= melissa_end + travel_ggp_to_rd)
    s.add(nancy_start >= emily_end + travel_rd_to_presidio)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        melissa_s = model.eval(melissa_start).as_long()
        melissa_e = model.eval(melissa_end).as_long()
        emily_s = model.eval(emily_start).as_long()
        emily_e = model.eval(emily_end).as_long()
        nancy_s = model.eval(nancy_start).as_long()
        nancy_e = model.eval(nancy_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Melissa", "start_time": minutes_to_time(melissa_s), "end_time": minutes_to_time(melissa_e)},
            {"action": "meet", "person": "Emily", "start_time": minutes_to_time(emily_s), "end_time": minutes_to_time(emily_e)},
            {"action": "meet", "person": "Nancy", "start_time": minutes_to_time(nancy_s), "end_time": minutes_to_time(nancy_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(solution)