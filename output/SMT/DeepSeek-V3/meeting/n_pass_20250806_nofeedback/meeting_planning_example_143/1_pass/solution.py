from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Meeting durations in minutes
    karen_min_duration = 90
    mark_min_duration = 120

    # Convert all times to minutes since 00:00 for easier arithmetic
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Availability windows
    karen_start = time_to_minutes("18:45")  # 6:45 PM
    karen_end = time_to_minutes("20:15")    # 8:15 PM
    mark_start = time_to_minutes("13:00")   # 1:00 PM
    mark_end = time_to_minutes("17:45")     # 5:45 PM

    # Current location: start at North Beach at 9:00 AM
    current_time = time_to_minutes("09:00")
    current_location = "North Beach"

    # Variables for meeting start and end times
    meet_mark_start = Int('meet_mark_start')
    meet_mark_end = Int('meet_mark_end')
    meet_karen_start = Int('meet_karen_start')
    meet_karen_end = Int('meet_karen_end')

    # Constraints for Mark's meeting
    s.add(meet_mark_start >= mark_start)
    s.add(meet_mark_end <= mark_end)
    s.add(meet_mark_end - meet_mark_start >= mark_min_duration)

    # Constraints for Karen's meeting
    s.add(meet_karen_start >= karen_start)
    s.add(meet_karen_end <= karen_end)
    s.add(meet_karen_end - meet_karen_start >= karen_min_duration)

    # Travel times
    # From North Beach to Pacific Heights: 8 min
    # From North Beach to Embarcadero: 6 min
    # From Pacific Heights to North Beach: 9 min
    # From Pacific Heights to Embarcadero: 10 min
    # From Embarcadero to North Beach: 5 min
    # From Embarcadero to Pacific Heights: 11 min

    # Determine the order of meetings and travel times
    # We have two options: meet Mark first or Karen first.
    # But Karen's availability is only in the evening, so meeting Mark first is the only feasible option.

    # Scenario: Meet Mark first, then Karen
    travel_to_mark = 6  # North Beach to Embarcadero
    s.add(meet_mark_start >= current_time + travel_to_mark)

    # Travel from Embarcadero to Pacific Heights: 11 min
    travel_to_karen = 11
    s.add(meet_karen_start >= meet_mark_end + travel_to_karen)

    # Check if the scenario is feasible
    if s.check() == sat:
        m = s.model()
        mark_s = m.eval(meet_mark_start).as_long()
        mark_e = m.eval(meet_mark_end).as_long()
        karen_s = m.eval(meet_karen_start).as_long()
        karen_e = m.eval(meet_karen_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Mark", "start_time": minutes_to_time(mark_s), "end_time": minutes_to_time(mark_e)},
            {"action": "meet", "person": "Karen", "start_time": minutes_to_time(karen_s), "end_time": minutes_to_time(karen_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(json.dumps(result, indent=2))