from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times
    meet_mark_start = Int('meet_mark_start')
    meet_mark_end = Int('meet_mark_end')
    meet_karen_start = Int('meet_karen_start')
    meet_karen_end = Int('meet_karen_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    mark_available_start = 13 * 60  # 1:00 PM
    mark_available_end = 17 * 60 + 45  # 5:45 PM
    karen_available_start = 18 * 60 + 45  # 6:45 PM
    karen_available_end = 20 * 60 + 15  # 8:15 PM

    # Add constraints for Mark's meeting
    s.add(meet_mark_start >= mark_available_start)
    s.add(meet_mark_end <= mark_available_end)
    s.add(meet_mark_end - meet_mark_start >= 120)  # 120 minutes minimum

    # Add constraints for Karen's meeting
    s.add(meet_karen_start >= karen_available_start)
    s.add(meet_karen_end <= karen_available_end)
    s.add(meet_karen_end - meet_karen_start >= 90)  # 90 minutes minimum

    # Travel times (in minutes)
    # From North Beach (starting point) to Pacific Heights: 8
    # From North Beach to Embarcadero: 6
    # From Pacific Heights to North Beach: 9
    # From Pacific Heights to Embarcadero: 10
    # From Embarcadero to North Beach: 5
    # From Embarcadero to Pacific Heights: 11

    # Assume we go directly to meet Mark first (Embarcadero), then to Karen (Pacific Heights)
    # Time to reach Mark: 6 minutes (from North Beach to Embarcadero)
    s.add(meet_mark_start >= 9 * 60 + 6)  # Arrive at North Beach at 9:00 AM (540 minutes)

    # Time to go from Embarcadero to Pacific Heights: 11 minutes
    s.add(meet_karen_start >= meet_mark_end + 11)

    # Alternatively, if we meet Karen first, but her availability is later, so this is not feasible

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        mark_start = m.eval(meet_mark_start).as_long()
        mark_end = m.eval(meet_mark_end).as_long()
        karen_start = m.eval(meet_karen_start).as_long()
        karen_end = m.eval(meet_karen_end).as_long()

        # Convert minutes back to HH:MM format
        def to_time_str(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Mark", "start_time": to_time_str(mark_start), "end_time": to_time_str(mark_end)},
            {"action": "meet", "person": "Karen", "start_time": to_time_str(karen_start), "end_time": to_time_str(karen_end)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(solution)