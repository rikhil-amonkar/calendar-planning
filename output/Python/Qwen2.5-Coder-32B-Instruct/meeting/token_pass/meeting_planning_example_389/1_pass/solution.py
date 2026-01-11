import json
from datetime import datetime, timedelta

# Define travel times between locations
travel_times = {
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Bayview"): 26,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Bayview"): 15,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Mission District"): 13,
}

# Define friends' availability and meeting constraints
friends = {
    "Sarah": {"location": "Fisherman's Wharf", "available": (14 * 60 + 45, 17 * 60 + 30), "min_duration": 105},
    "Mary": {"location": "Richmond District", "available": (13 * 60, 19 * 60 + 15), "min_duration": 75},
    "Helen": {"location": "Mission District", "available": (21 * 60 + 45, 22 * 60 + 30), "min_duration": 30},
    "Thomas": {"location": "Bayview", "available": (15 * 60 + 15, 18 * 60 + 45), "min_duration": 120},
}

def time_to_minutes(time_str):
    return int(time_str[:2]) * 60 + int(time_str[3:])

def minutes_to_time(minutes):
    hours, minutes = divmod(minutes, 60)
    return f"{hours}:{minutes:02}"

def find_optimal_schedule(start_location, start_time):
    current_location = start_location
    current_time = start_time
    itinerary = []

    # Sort friends by their earliest available time
    sorted_friends = sorted(friends.items(), key=lambda x: x[1]['available'][0])

    for name, details in sorted_friends:
        location = details['location']
        available_start, available_end = details['available']
        min_duration = details['min_duration']

        # Calculate travel time to the friend's location
        travel_time = travel_times[(current_location, location)]

        # Calculate the earliest possible start time for the meeting
        earliest_meeting_start = max(current_time + travel_time, available_start)

        # Calculate the latest possible end time for the meeting
        latest_meeting_end = min(available_end, earliest_meeting_start + min_duration)

        # Check if the meeting can fit within the available time
        if earliest_meeting_start + min_duration <= available_end:
            # Schedule the meeting
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time(earliest_meeting_start),
                "end_time": minutes_to_time(latest_meeting_end)
            })
            # Update current location and time
            current_location = location
            current_time = latest_meeting_end

    return itinerary

# Initial start location and time
start_location = "Haight-Ashbury"
start_time = 540  # 9:00 AM

# Find the optimal schedule
optimal_itinerary = find_optimal_schedule(start_location, start_time)

# Output the result as JSON
result = {"itinerary": optimal_itinerary}
print(json.dumps(result, indent=2))