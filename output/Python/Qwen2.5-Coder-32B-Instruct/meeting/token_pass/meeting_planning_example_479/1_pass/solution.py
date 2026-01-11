import json
from datetime import datetime, timedelta

# Define travel times as a dictionary of dictionaries
travel_times = {
    "Embarcadero": {"Golden Gate Park": 25, "Haight-Ashbury": 21, "Bayview": 21, "Presidio": 20, "Financial District": 5},
    "Golden Gate Park": {"Embarcadero": 25, "Haight-Ashbury": 7, "Bayview": 23, "Presidio": 11, "Financial District": 26},
    "Haight-Ashbury": {"Embarcadero": 20, "Golden Gate Park": 7, "Bayview": 18, "Presidio": 15, "Financial District": 21},
    "Bayview": {"Embarcadero": 19, "Golden Gate Park": 22, "Haight-Ashbury": 19, "Presidio": 31, "Financial District": 19},
    "Presidio": {"Embarcadero": 20, "Golden Gate Park": 12, "Haight-Ashbury": 15, "Bayview": 31, "Financial District": 23},
    "Financial District": {"Embarcadero": 4, "Golden Gate Park": 23, "Haight-Ashbury": 19, "Bayview": 19, "Presidio": 22}
}

# Define friends' availability and minimum meeting durations
friends = {
    "Mary": {"location": "Golden Gate Park", "start_time": "8:45", "end_time": "11:45", "min_duration": 45},
    "Kevin": {"location": "Haight-Ashbury", "start_time": "10:15", "end_time": "16:15", "min_duration": 90},
    "Deborah": {"location": "Bayview", "start_time": "15:00", "end_time": "19:15", "min_duration": 120},
    "Stephanie": {"location": "Presidio", "start_time": "10:00", "end_time": "17:15", "min_duration": 120},
    "Emily": {"location": "Financial District", "start_time": "11:30", "end_time": "21:45", "min_duration": 105}
}

def time_to_minutes(time_str):
    """Convert time in 'H:MM' format to minutes since midnight."""
    return int(time_str.split(':')[0]) * 60 + int(time_str.split(':')[1])

def minutes_to_time(minutes):
    """Convert minutes since midnight to time in 'H:MM' format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def find_feasible_meeting(current_time, current_location, friend_info):
    """Determine if a meeting with a friend is feasible and return meeting details if so."""
    friend_location = friend_info["location"]
    travel_time = travel_times[current_location][friend_location]
    friend_start = time_to_minutes(friend_info["start_time"])
    friend_end = time_to_minutes(friend_info["end_time"])
    min_duration = friend_info["min_duration"]

    # Calculate earliest possible meeting start time
    earliest_start = max(current_time + travel_time, friend_start)

    # Check if there's enough time to meet
    if earliest_start + min_duration <= friend_end:
        meeting_start = earliest_start
        meeting_end = meeting_start + min_duration
        return {
            "action": "meet",
            "location": friend_location,
            "person": list(friends.keys())[list(friends.values()).index(friend_info)],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
    return None

def generate_itinerary(start_time, start_location):
    """Generate the optimal meeting itinerary."""
    current_time = time_to_minutes(start_time)
    current_location = start_location
    itinerary = []

    # Sort friends by their start times to prioritize earlier meetings
    sorted_friends = sorted(friends.items(), key=lambda x: time_to_minutes(x[1]["start_time"]))

    for friend_name, friend_info in sorted_friends:
        meeting = find_feasible_meeting(current_time, current_location, friend_info)
        if meeting:
            itinerary.append(meeting)
            current_time = time_to_minutes(meeting["end_time"])
            current_location = meeting["location"]

    return itinerary

# Generate the itinerary starting from Embarcadero at 9:00 AM
itinerary = generate_itinerary("9:00", "Embarcadero")

# Output the result as a JSON-formatted dictionary
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))