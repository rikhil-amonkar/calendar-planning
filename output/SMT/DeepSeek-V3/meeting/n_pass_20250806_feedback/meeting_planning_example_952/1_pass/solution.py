from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Matthew", "location": "Presidio", "start_window": "8:15", "end_window": "9:00", "min_duration": 15},
        {"name": "Richard", "location": "Fisherman's Wharf", "start_window": "11:00", "end_window": "12:45", "min_duration": 60},
        {"name": "Elizabeth", "location": "Nob Hill", "start_window": "11:45", "end_window": "6:30", "min_duration": 75},
        {"name": "Anthony", "location": "Pacific Heights", "start_window": "2:15", "end_window": "4:00", "min_duration": 30},
        {"name": "Brian", "location": "North Beach", "start_window": "1:00", "end_window": "7:00", "min_duration": 90},
        {"name": "Kenneth", "location": "Chinatown", "start_window": "1:45", "end_window": "7:30", "min_duration": 105},
        {"name": "Ashley", "location": "Haight-Ashbury", "start_window": "3:00", "end_window": "8:30", "min_duration": 90},
        {"name": "Kimberly", "location": "Alamo Square", "start_window": "5:30", "end_window": "9:15", "min_duration": 45},
        {"name": "Deborah", "location": "Union Square", "start_window": "5:30", "end_window": "10:00", "min_duration": 60},
        {"name": "Jessica", "location": "Golden Gate Park", "start_window": "8:00", "end_window": "9:45", "min_duration": 105}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each friend: start and end times in minutes since 9:00 AM (540)
    for friend in friends:
        start_window = time_to_minutes(friend["start_window"])
        end_window = time_to_minutes(friend["end_window"])
        friend["start_var"] = Int(f"start_{friend['name']}")
        friend["end_var"] = Int(f"end_{friend['name']}")
        s.add(friend["start_var"] >= start_window - 540)
        s.add(friend["end_var"] <= end_window - 540)
        s.add(friend["end_var"] - friend["start_var"] >= friend["min_duration"])

    # Current location starts at Bayview at time 0 (9:00 AM)
    current_location = "Bayview"
    current_time = 0

    # Define travel times dictionary for quick lookup
    travel_times = {
        "Bayview": {
            "North Beach": 22,
            "Fisherman's Wharf": 25,
            "Haight-Ashbury": 19,
            "Nob Hill": 20,
            "Golden Gate Park": 22,
            "Union Square": 18,
            "Alamo Square": 16,
            "Presidio": 32,
            "Chinatown": 19,
            "Pacific Heights": 23
        },
        "North Beach": {
            "Bayview": 25,
            "Fisherman's Wharf": 5,
            "Haight-Ashbury": 18,
            "Nob Hill": 7,
            "Golden Gate Park": 22,
            "Union Square": 7,
            "Alamo Square": 16,
            "Presidio": 17,
            "Chinatown": 6,
            "Pacific Heights": 8
        },
        "Fisherman's Wharf": {
            "Bayview": 26,
            "North Beach": 6,
            "Haight-Ashbury": 22,
            "Nob Hill": 11,
            "Golden Gate Park": 25,
            "Union Square": 13,
            "Alamo Square": 21,
            "Presidio": 17,
            "Chinatown": 12,
            "Pacific Heights": 12
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "North Beach": 19,
            "Fisherman's Wharf": 23,
            "Nob Hill": 15,
            "Golden Gate Park": 7,
            "Union Square": 19,
            "Alamo Square": 5,
            "Presidio": 15,
            "Chinatown": 19,
            "Pacific Heights": 12
        },
        "Nob Hill": {
            "Bayview": 19,
            "North Beach": 8,
            "Fisherman's Wharf": 10,
            "Haight-Ashbury": 13,
            "Golden Gate Park": 17,
            "Union Square": 7,
            "Alamo Square": 11,
            "Presidio": 17,
            "Chinatown": 6,
            "Pacific Heights": 8
        },
        "Golden Gate Park": {
            "Bayview": 23,
            "North Beach": 23,
            "Fisherman's Wharf": 24,
            "Haight-Ashbury": 7,
            "Nob Hill": 20,
            "Union Square": 22,
            "Alamo Square": 9,
            "Presidio": 11,
            "Chinatown": 23,
            "Pacific Heights": 16
        },
        "Union Square": {
            "Bayview": 15,
            "North Beach": 10,
            "Fisherman's Wharf": 15,
            "Haight-Ashbury": 18,
            "Nob Hill": 9,
            "Golden Gate Park": 22,
            "Alamo Square": 15,
            "Presidio": 24,
            "Chinatown": 7,
            "Pacific Heights": 15
        },
        "Alamo Square": {
            "Bayview": 16,
            "North Beach": 15,
            "Fisherman's Wharf": 19,
            "Haight-Ashbury": 5,
            "Nob Hill": 11,
            "Golden Gate Park": 9,
            "Union Square": 14,
            "Presidio": 17,
            "Chinatown": 15,
            "Pacific Heights": 10
        },
        "Presidio": {
            "Bayview": 31,
            "North Beach": 18,
            "Fisherman's Wharf": 19,
            "Haight-Ashbury": 15,
            "Nob Hill": 18,
            "Golden Gate Park": 12,
            "Union Square": 22,
            "Alamo Square": 19,
            "Chinatown": 21,
            "Pacific Heights": 11
        },
        "Chinatown": {
            "Bayview": 20,
            "North Beach": 3,
            "Fisherman's Wharf": 8,
            "Haight-Ashbury": 19,
            "Nob Hill": 9,
            "Golden Gate Park": 23,
            "Union Square": 7,
            "Alamo Square": 17,
            "Presidio": 19,
            "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Bayview": 22,
            "North Beach": 9,
            "Fisherman's Wharf": 13,
            "Haight-Ashbury": 11,
            "Nob Hill": 8,
            "Golden Gate Park": 15,
            "Union Square": 12,
            "Alamo Square": 10,
            "Presidio": 11,
            "Chinatown": 11
        }
    }

    # Define the order of meetings (this is a heuristic; in practice, we'd need to explore permutations)
    # For simplicity, we'll try to meet friends in the order of their earliest possible start times
    friends_sorted = sorted(friends, key=lambda x: time_to_minutes(x["start_window"]))

    # Create variables to track the order of meetings
    # We'll use a list to represent the sequence of meetings
    # For each possible meeting, we'll have a variable indicating whether it's included in the itinerary
    included = [Bool(f"included_{friend['name']}") for friend in friends_sorted]

    # Ensure at least one meeting is included
    s.add(Or(included))

    # For each friend, if included, their start time must be after the previous meeting's end time plus travel time
    previous_end = 0
    previous_location = "Bayview"
    itinerary_order = []

    for i, friend in enumerate(friends_sorted):
        # If this friend is included, their start time must be >= previous_end + travel time
        travel_time = travel_times[previous_location][friend["location"]]
        s.add(Implies(included[i], friend["start_var"] >= previous_end + travel_time))
        # Update previous_end and previous_location if this friend is included
        new_previous_end = If(included[i], friend["end_var"], previous_end)
        new_previous_location = If(included[i], friend["location"], previous_location)
        previous_end = new_previous_end
        previous_location = new_previous_location
        itinerary_order.append((included[i], friend))

    # Maximize the number of friends met
    # We can also try to maximize the total meeting time, but for simplicity, we'll maximize the count
    total_met = Sum([If(included[i], 1, 0) for i in range(len(included))])
    s.maximize(total_met)

    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i, friend in enumerate(friends_sorted):
            if model.evaluate(included[i]):
                start = model.evaluate(friend["start_var"]).as_long() + 540
                end = model.evaluate(friend["end_var"]).as_long() + 540
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))