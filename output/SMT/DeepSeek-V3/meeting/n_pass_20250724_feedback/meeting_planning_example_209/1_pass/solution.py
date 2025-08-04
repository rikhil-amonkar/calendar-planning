from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define time variables in minutes since 9:00 AM (540 minutes)
    # Meeting with Melissa
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')
    # Meeting with Anthony
    anthony_start = Int('anthony_start')
    anthony_end = Int('anthony_end')
    # Meeting with Rebecca
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')

    # Convert friend's available times to minutes since 9:00 AM
    # Melissa: 8:15 AM to 1:30 PM (since 9:00 AM is 0, 8:15 AM is -45, 1:30 PM is 270)
    melissa_available_start = -45  # 8:15 AM is 45 minutes before 9:00 AM
    melissa_available_end = 270    # 1:30 PM is 270 minutes after 9:00 AM

    # Anthony: 1:15 PM to 2:30 PM (255 to 330 minutes)
    anthony_available_start = 255  # 1:15 PM is 255 minutes after 9:00 AM
    anthony_available_end = 330    # 2:30 PM is 330 minutes after 9:00 AM

    # Rebecca: 7:30 PM to 9:15 PM (630 to 735 minutes)
    rebecca_available_start = 630  # 7:30 PM is 630 minutes after 9:00 AM
    rebecca_available_end = 735    # 9:15 PM is 735 minutes after 9:00 AM

    # Minimum durations in minutes
    melissa_min_duration = 105
    anthony_min_duration = 60
    rebecca_min_duration = 105

    # Constraints for Melissa
    s.add(melissa_start >= melissa_available_start)
    s.add(melissa_end <= melissa_available_end)
    s.add(melissa_end - melissa_start >= melissa_min_duration)

    # Constraints for Anthony
    s.add(anthony_start >= anthony_available_start)
    s.add(anthony_end <= anthony_available_end)
    s.add(anthony_end - anthony_start >= anthony_min_duration)

    # Constraints for Rebecca
    s.add(rebecca_start >= rebecca_available_start)
    s.add(rebecca_end <= rebecca_available_end)
    s.add(rebecca_end - rebecca_start >= rebecca_min_duration)

    # Travel times (in minutes)
    # From Sunset to North Beach (Melissa's location): 29 minutes
    travel_sunset_to_north_beach = 29
    # From North Beach to Chinatown (Anthony's location): 6 minutes
    travel_north_beach_to_chinatown = 6
    # From Chinatown to Russian Hill (Rebecca's location): 7 minutes
    travel_chinatown_to_russian_hill = 7

    # Ensure time ordering and travel times
    # Start at Sunset at 9:00 AM (0 minutes)
    # Then go to North Beach to meet Melissa
    s.add(melissa_start >= travel_sunset_to_north_beach)

    # After Melissa, go to Chinatown to meet Anthony
    s.add(anthony_start >= melissa_end + travel_north_beach_to_chinatown)

    # After Anthony, go to Russian Hill to meet Rebecca
    s.add(rebecca_start >= anthony_end + travel_chinatown_to_russian_hill)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        melissa_s = m.eval(melissa_start).as_long()
        melissa_e = m.eval(melissa_end).as_long()
        anthony_s = m.eval(anthony_start).as_long()
        anthony_e = m.eval(anthony_end).as_long()
        rebecca_s = m.eval(rebecca_start).as_long()
        rebecca_e = m.eval(rebecca_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Melissa", "start_time": minutes_to_time(melissa_s), "end_time": minutes_to_time(melissa_e)},
            {"action": "meet", "person": "Anthony", "start_time": minutes_to_time(anthony_s), "end_time": minutes_to_time(anthony_e)},
            {"action": "meet", "person": "Rebecca", "start_time": minutes_to_time(rebecca_s), "end_time": minutes_to_time(rebecca_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute and print the solution
solution = solve_scheduling()
print(solution)