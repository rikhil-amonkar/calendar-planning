from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations
    locations = ['Fishermans_Wharf', 'Golden_Gate_Park', 'Presidio', 'Richmond_District']
    
    # Define the travel times (in minutes) as a dictionary of dictionaries
    travel_times = {
        'Fishermans_Wharf': {
            'Golden_Gate_Park': 25,
            'Presidio': 17,
            'Richmond_District': 18
        },
        'Golden_Gate_Park': {
            'Fishermans_Wharf': 24,
            'Presidio': 11,
            'Richmond_District': 7
        },
        'Presidio': {
            'Fishermans_Wharf': 19,
            'Golden_Gate_Park': 12,
            'Richmond_District': 7
        },
        'Richmond_District': {
            'Fishermans_Wharf': 18,
            'Golden_Gate_Park': 9,
            'Presidio': 7
        }
    }

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Melissa's availability: 8:30 AM (510) to 8:00 PM (1200)
    melissa_start_avail = 510  # 8:30 AM in minutes since midnight
    melissa_end_avail = 1200    # 8:00 PM in minutes since midnight
    melissa_min_duration = 15   # minutes

    # Nancy's availability: 7:45 PM (1185) to 10:00 PM (1320)
    nancy_start_avail = 1185    # 7:45 PM in minutes since midnight
    nancy_end_avail = 1320      # 10:00 PM in minutes since midnight
    nancy_min_duration = 105    # minutes

    # Emily's availability: 4:45 PM (1005) to 10:00 PM (1320)
    emily_start_avail = 1005    # 4:45 PM in minutes since midnight
    emily_end_avail = 1320      # 10:00 PM in minutes since midnight
    emily_min_duration = 120    # minutes

    # Current time starts at 9:00 AM (540 minutes since midnight) at Fisherman's Wharf
    current_time = 540
    current_location = 'Fishermans_Wharf'

    # Variables for meeting start and end times
    meet_melissa_start = Int('meet_melissa_start')
    meet_melissa_end = Int('meet_melissa_end')
    meet_nancy_start = Int('meet_nancy_start')
    meet_nancy_end = Int('meet_nancy_end')
    meet_emily_start = Int('meet_emily_start')
    meet_emily_end = Int('meet_emily_end')

    # Constraints for Melissa
    s.add(meet_melissa_start >= melissa_start_avail)
    s.add(meet_melissa_end <= melissa_end_avail)
    s.add(meet_melissa_end - meet_melissa_start >= melissa_min_duration)

    # Constraints for Nancy
    s.add(meet_nancy_start >= nancy_start_avail)
    s.add(meet_nancy_end <= nancy_end_avail)
    s.add(meet_nancy_end - meet_nancy_start >= nancy_min_duration)

    # Constraints for Emily
    s.add(meet_emily_start >= emily_start_avail)
    s.add(meet_emily_end <= emily_end_avail)
    s.add(meet_emily_end - meet_emily_start >= emily_min_duration)

    # Order of meetings and travel times
    # We need to decide the order in which to meet the friends. Let's assume the order is Melissa -> Emily -> Nancy.
    # This is a reasonable order given the time windows.
    # Alternatively, we could model the order as a variable, but for simplicity, we'll fix the order here.

    # Travel from Fisherman's Wharf to Golden Gate Park to meet Melissa
    s.add(meet_melissa_start >= current_time + travel_times[current_location]['Golden_Gate_Park'])
    # After meeting Melissa, travel to the next location (Emily is in Richmond District)
    s.add(meet_emily_start >= meet_melissa_end + travel_times['Golden_Gate_Park']['Richmond_District'])
    # After meeting Emily, travel to Nancy (Presidio)
    s.add(meet_nancy_start >= meet_emily_end + travel_times['Richmond_District']['Presidio'])

    # Ensure no overlaps
    s.add(meet_melissa_end <= meet_emily_start)
    s.add(meet_emily_end <= meet_nancy_start)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        melissa_start = m.eval(meet_melissa_start).as_long()
        melissa_end = m.eval(meet_melissa_end).as_long()
        emily_start = m.eval(meet_emily_start).as_long()
        emily_end = m.eval(meet_emily_end).as_long()
        nancy_start = m.eval(meet_nancy_start).as_long()
        nancy_end = m.eval(meet_nancy_end).as_long()

        print("SOLUTION:")
        print(f"Meet Melissa at Golden Gate Park from {minutes_to_time(melissa_start)} to {minutes_to_time(melissa_end)}")
        print(f"Meet Emily at Richmond District from {minutes_to_time(emily_start)} to {minutes_to_time(emily_end)}")
        print(f"Meet Nancy at Presidio from {minutes_to_time(nancy_start)} to {minutes_to_time(nancy_end)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()