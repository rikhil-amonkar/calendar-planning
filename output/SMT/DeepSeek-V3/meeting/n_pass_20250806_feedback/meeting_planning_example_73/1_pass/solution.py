from z3 import *

def solve_scheduling():
    s = Solver()

    # Define variables for the start and end times of the meeting with Barbara
    start_barbara = Int('start_barbara')
    end_barbara = Int('end_barbara')

    # Constraints for Barbara's availability (7:15 AM to 10:00 PM)
    barbara_available_start = 7 * 60 + 15  # 7:15 AM
    barbara_available_end = 22 * 60        # 10:00 PM

    # You arrive at Russian Hill at 9:00 AM (540 minutes since midnight)
    arrival_time = 9 * 60

    # Travel time from Russian Hill to Pacific Heights is 7 minutes
    travel_time = 7

    # Minimum meeting duration is 60 minutes
    min_duration = 60

    # Constraints:
    s.add(start_barbara >= arrival_time + travel_time)
    s.add(end_barbara >= start_barbara + min_duration)
    s.add(start_barbara >= barbara_available_start)
    s.add(end_barbara <= barbara_available_end)
    s.add(end_barbara > start_barbara)

    # Minimize the start time to meet as early as possible
    s.minimize(start_barbara)

    if s.check() == sat:
        m = s.model()
        start = m.eval(start_barbara).as_long()
        end = m.eval(end_barbara).as_long()

        def minutes_to_time(minutes):
            hours = minutes // 60
            minutes = minutes % 60
            return f"{hours:02d}:{minutes:02d}"

        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)

        itinerary = [
            {"action": "meet", "person": "Barbara", "start_time": start_time, "end_time": end_time}
        ]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(result)