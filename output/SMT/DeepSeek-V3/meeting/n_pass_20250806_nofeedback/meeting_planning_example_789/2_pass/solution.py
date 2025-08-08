from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Betty", "location": "Russian Hill", "available_start": 7*60, "available_end": 16*60 + 45, "min_duration": 105},
        {"name": "Melissa", "location": "Alamo Square", "available_start": 9*60 + 30, "available_end": 17*60 + 15, "min_duration": 105},
        {"name": "Joshua", "location": "Haight-Ashbury", "available_start": 12*60 + 15, "available_end": 19*60, "min_duration": 90},
        {"name": "Jeffrey", "location": "Marina District", "available_start": 12*60 + 15, "available_end": 18*60, "min_duration": 45},
        {"name": "James", "location": "Bayview", "available_start": 7*60 + 30, "available_end": 20*60, "min_duration": 90},
        {"name": "Anthony", "location": "Chinatown", "available_start": 11*60 + 45, "available_end": 13*60 + 30, "min_duration": 75},
        {"name": "Timothy", "location": "Presidio", "available_start": 12*60 + 30, "available_end": 14*60 + 45, "min_duration": 90},
        {"name": "Emily", "location": "Sunset District", "available_start": 19*60 + 30, "available_end": 21*60 + 30, "min_duration": 120}
    ]

    # Create variables for each friend's meeting start and end times (in minutes since 9:00 AM)
    start_vars = {}
    end_vars = {}
    for friend in friends:
        name = friend["name"]
        start_vars[name] = Int(f'start_{name}')
        end_vars[name] = Int(f'end_{name}')

    # Define travel times between locations (in minutes)
    travel_times = {
        "Union Square": {
            "Russian Hill": 13,
            "Alamo Square": 15,
            "Haight-Ashbury": 18,
            "Marina District": 18,
            "Bayview": 15,
            "Chinatown": 7,
            "Presidio": 24,
            "Sunset District": 27
        },
        "Russian Hill": {
            "Union Square": 10,
            "Alamo Square": 15,
            "Haight-Ashbury": 17,
            "Marina District": 7,
            "Bayview": 23,
            "Chinatown": 9,
            "Presidio": 14,
            "Sunset District": 23
        },
        "Alamo Square": {
            "Union Square": 14,
            "Russian Hill": 13,
            "Haight-Ashbury": 5,
            "Marina District": 15,
            "Bayview": 16,
            "Chinatown": 15,
            "Presidio": 17,
            "Sunset District": 16
        },
        "Haight-Ashbury": {
            "Union Square": 19,
            "Russian Hill": 17,
            "Alamo Square": 5,
            "Marina District": 17,
            "Bayview": 18,
            "Chinatown": 19,
            "Presidio": 15,
            "Sunset District": 15
        },
        "Marina District": {
            "Union Square": 16,
            "Russian Hill": 8,
            "Alamo Square": 15,
            "Haight-Ashbury": 16,
            "Bayview": 27,
            "Chinatown": 15,
            "Presidio": 10,
            "Sunset District": 19
        },
        "Bayview": {
            "Union Square": 18,
            "Russian Hill": 23,
            "Alamo Square": 16,
            "Haight-Ashbury": 19,
            "Marina District": 27,
            "Chinatown": 19,
            "Presidio": 32,
            "Sunset District": 23
        },
        "Chinatown": {
            "Union Square": 7,
            "Russian Hill": 7,
            "Alamo Square": 17,
            "Haight-Ashbury": 19,
            "Marina District": 12,
            "Bayview": 20,
            "Presidio": 19,
            "Sunset District": 29
        },
        "Presidio": {
            "Union Square": 22,
            "Russian Hill": 14,
            "Alamo Square": 19,
            "Haight-Ashbury": 15,
            "Marina District": 11,
            "Bayview": 31,
            "Chinatown": 21,
            "Sunset District": 15
        },
        "Sunset District": {
            "Union Square": 30,
            "Russian Hill": 24,
            "Alamo Square": 17,
            "Haight-Ashbury": 15,
            "Marina District": 21,
            "Bayview": 22,
            "Chinatown": 30,
            "Presidio": 16
        }
    }

    # Current location starts at Union Square at time 0 (9:00 AM)
    current_location = "Union Square"
    current_time = 0  # 9:00 AM is 0 minutes

    # Constraints for each friend's meeting
    for friend in friends:
        name = friend["name"]
        available_start = friend["available_start"] - 9*60  # Convert to minutes since 9:00 AM
        available_end = friend["available_end"] - 9*60
        min_duration = friend["min_duration"]

        # Meeting must start and end within the friend's availability
        s.add(start_vars[name] >= available_start)
        s.add(end_vars[name] <= available_end)
        s.add(end_vars[name] >= start_vars[name] + min_duration)

    # Define the order of meetings using a list of integers representing the sequence
    num_friends = len(friends)
    order = [Int(f'order_{i}') for i in range(num_friends)]

    # Each order variable must be between 0 and num_friends - 1
    for o in order:
        s.add(o >= 0)
        s.add(o < num_friends)

    # All order variables must be distinct
    s.add(Distinct(order))

    # Add constraints for travel times between consecutive meetings in the order
    for i in range(num_friends - 1):
        current_order = order[i]
        next_order = order[i + 1]
        # Get the current and next friend based on order
        current_friend = friends[current_order]
        next_friend = friends[next_order]
        # Get travel time between current and next location
        travel_time = travel_times[current_friend["location"]][next_friend["location"]]
        # Add constraint: start of next meeting >= end of current meeting + travel time
        s.add(start_vars[next_friend["name"]] >= end_vars[current_friend["name"]] + travel_time)

    # Initial travel from Union Square to first meeting
    first_order = order[0]
    first_friend = friends[first_order]
    travel_time = travel_times["Union Square"][first_friend["location"]]
    s.add(start_vars[first_friend["name"]] >= travel_time)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            name = friend["name"]
            start = model.evaluate(start_vars[name]).as_long()
            end = model.evaluate(end_vars[name]).as_long()
            # Convert minutes since 9:00 AM to HH:MM format
            start_hh = (9 * 60 + start) // 60
            start_mm = (9 * 60 + start) % 60
            end_hh = (9 * 60 + end) // 60
            end_mm = (9 * 60 + end) % 60
            start_time = f"{start_hh:02d}:{start_mm:02d}"
            end_time = f"{end_hh:02d}:{end_mm:02d}"
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print("SOLUTION:")
print(result)