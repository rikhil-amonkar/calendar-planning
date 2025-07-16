from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations
    locations = {
        'Fishermans_Wharf': 0,
        'Golden_Gate_Park': 1,
        'Presidio': 2,
        'Richmond_District': 3
    }

    # Travel times in minutes (from_location, to_location) -> time
    travel_times = {
        (0, 1): 25,
        (0, 2): 17,
        (0, 3): 18,
        (1, 0): 24,
        (1, 2): 11,
        (1, 3): 7,
        (2, 0): 19,
        (2, 1): 12,
        (2, 3): 7,
        (3, 0): 18,
        (3, 1): 9,
        (3, 2): 7
    }

    # Convert all times to minutes since 9:00 AM (540 minutes)
    start_of_day = 540  # 9:00 AM in minutes

    # Meeting constraints
    # Melissa: Golden Gate Park, 8:30 AM (510) to 8:00 PM (1200), min 15 minutes
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')
    s.add(melissa_start >= 510)  # 8:30 AM
    s.add(melissa_end <= 1200)   # 8:00 PM
    s.add(melissa_end - melissa_start >= 15)

    # Nancy: Presidio, 7:45 PM (1185) to 10:00 PM (1320), min 105 minutes
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')
    s.add(nancy_start >= 1185)   # 7:45 PM
    s.add(nancy_end <= 1320)     # 10:00 PM
    s.add(nancy_end - nancy_start >= 105)

    # Emily: Richmond District, 4:45 PM (1065) to 10:00 PM (1320), min 120 minutes
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    s.add(emily_start >= 1065)    # 4:45 PM
    s.add(emily_end <= 1320)      # 10:00 PM
    s.add(emily_end - emily_start >= 120)

    # Starting at Fisherman's Wharf at 9:00 AM (540)
    current_time = 540
    current_location = 0  # Fisherman's Wharf

    # Travel to Golden Gate Park to meet Melissa
    travel_to_melissa = travel_times[(current_location, 1)]
    arrive_melissa = current_time + travel_to_melissa
    s.add(melissa_start >= arrive_melissa)
    # After meeting Melissa, update current_time and location
    post_melissa_time = melissa_end
    post_melissa_location = 1

    # Travel to Richmond District to meet Emily
    travel_to_emily = travel_times[(post_melissa_location, 3)]
    arrive_emily = post_melissa_time + travel_to_emily
    s.add(emily_start >= arrive_emily)
    # After meeting Emily, update current_time and location
    post_emily_time = emily_end
    post_emily_location = 3

    # Travel to Presidio to meet Nancy
    travel_to_nancy = travel_times[(post_emily_location, 2)]
    arrive_nancy = post_emily_time + travel_to_nancy
    s.add(nancy_start >= arrive_nancy)

    # Check if the schedule is possible
    if s.check() == sat:
        m = s.model()
        print("Found a valid schedule:")
        print(f"Meet Melissa from {m[melissa_start].as_long()} to {m[melissa_end].as_long()} (Golden Gate Park)")
        print(f"Meet Emily from {m[emily_start].as_long()} to {m[emily_end].as_long()} (Richmond District)")
        print(f"Meet Nancy from {m[nancy_start].as_long()} to {m[nancy_end].as_long()} (Presidio)")
    else:
        print("No valid schedule found.")

solve_scheduling()