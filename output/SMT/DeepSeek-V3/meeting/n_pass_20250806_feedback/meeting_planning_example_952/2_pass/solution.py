from itertools import permutations
import json

def solve_scheduling():
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

    # Generate all possible permutations of friends
    max_friends = len(friends)
    best_itinerary = []
    best_count = 0

    for perm in permutations(friends):
        current_location = "Bayview"
        current_time = 0
        itinerary = []
        count = 0

        for friend in perm:
            start_window = time_to_minutes(friend["start_window"]) - 540
            end_window = time_to_minutes(friend["end_window"]) - 540
            min_duration = friend["min_duration"]
            location = friend["location"]

            # Calculate travel time
            travel_time = travel_times[current_location][location]

            # Calculate earliest possible start time
            earliest_start = current_time + travel_time
            if earliest_start > end_window:
                continue  # Cannot meet this friend

            # Calculate latest possible start time
            latest_start = end_window - min_duration
            if latest_start < start_window:
                continue  # Cannot meet this friend

            # Choose the latest possible start time to maximize meeting duration
            start_time = max(earliest_start, start_window)
            end_time = start_time + min_duration

            if end_time > end_window:
                continue  # Cannot meet this friend

            # Add to itinerary
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": minutes_to_time(start_time + 540),
                "end_time": minutes_to_time(end_time + 540)
            })
            count += 1
            current_time = end_time
            current_location = location

        if count > best_count:
            best_count = count
            best_itinerary = itinerary

    return {"itinerary": best_itinerary}

# Run the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))