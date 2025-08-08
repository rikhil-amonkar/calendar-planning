from z3 import *
import datetime

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Base time: 9:00 AM in minutes
    base_time = time_to_minutes("09:00")

    # Define variables for meeting start and end times in minutes since base_time
    # Meeting with Mark at Embarcadero
    mark_start = Int('mark_start')  # minutes since 9:00 AM
    mark_end = Int('mark_end')

    # Meeting with Karen at Pacific Heights
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')

    # Mark's availability: 1:00 PM to 5:45 PM (13:00 to 17:45)
    mark_available_start = time_to_minutes("13:00") - base_time
    mark_available_end = time_to_minutes("17:45") - base_time

    # Karen's availability: 6:45 PM to 8:15 PM (18:45 to 20:15)
    karen_available_start = time_to_minutes("18:45") - base_time
    karen_available_end = time_to_minutes("20:15") - base_time

    # Add constraints for Mark's meeting
    s.add(mark_start >= mark_available_start)
    s.add(mark_end <= mark_available_end)
    s.add(mark_end - mark_start >= 120)  # 120 minutes minimum

    # Add constraints for Karen's meeting
    s.add(karen_start >= karen_available_start)
    s.add(karen_end <= karen_available_end)
    s.add(karen_end - karen_start >= 90)  # 90 minutes minimum

    # Travel times (in minutes)
    # From North Beach to Embarcadero: 6 minutes
    # From Embarcadero to Pacific Heights: 11 minutes
    # From Pacific Heights to North Beach: 9 minutes (not needed here)

    # Initial location: North Beach at 9:00 AM (time 0)
    # To meet Mark at Embarcadero, travel time is 6 minutes from North Beach
    s.add(mark_start >= 6)

    # After meeting Mark, travel to Pacific Heights takes 11 minutes
    s.add(karen_start >= mark_end + 11)

    # Ensure all times are non-negative
    s.add(mark_start >= 0, mark_end >= 0)
    s.add(karen_start >= 0, karen_end >= 0)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Get the values from the model
        mark_start_val = m.evaluate(mark_start).as_long()
        mark_end_val = m.evaluate(mark_end).as_long()
        karen_start_val = m.evaluate(karen_start).as_long()
        karen_end_val = m.evaluate(karen_end).as_long()

        # Convert back to absolute times
        def get_absolute_time(minutes):
            total_minutes = base_time + minutes
            hh = total_minutes // 60
            mm = total_minutes % 60
            return f"{hh:02d}:{mm:02d}"

        mark_start_time = get_absolute_time(mark_start_val)
        mark_end_time = get_absolute_time(mark_end_val)
        karen_start_time = get_absolute_time(karen_start_val)
        karen_end_time = get_absolute_time(karen_end_val)

        itinerary = [
            {"action": "meet", "person": "Mark", "start_time": mark_start_time, "end_time": mark_end_time},
            {"action": "meet", "person": "Karen", "start_time": karen_start_time, "end_time": karen_end_time}
        ]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(result)