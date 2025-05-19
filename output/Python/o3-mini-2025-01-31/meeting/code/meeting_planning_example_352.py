#!/usr/bin/env python3
import itertools
import json

# Helper functions to convert time strings to minutes-since-midnight and back.
def time_to_minutes(timestr):
    # expects format H:MM or HH:MM
    parts = timestr.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"  # hour without leading zero, minute always 2 digits

# Meeting constraints for each friend
friends = {
    "Karen": {
        "location": "Nob Hill",
        "available_start": time_to_minutes("21:15"),
        "available_end": time_to_minutes("21:45"),
        "min_duration": 30
    },
    "Joseph": {
        "location": "Haight-Ashbury",
        "available_start": time_to_minutes("12:30"),
        "available_end": time_to_minutes("19:45"),
        "min_duration": 90
    },
    "Sandra": {
        "location": "Chinatown",
        "available_start": time_to_minutes("7:15"),
        "available_end": time_to_minutes("19:15"),
        "min_duration": 75
    },
    "Nancy": {
        "location": "Marina District",
        "available_start": time_to_minutes("11:00"),
        "available_end": time_to_minutes("20:15"),
        "min_duration": 105
    }
}

# Travel distances (in minutes) as provided.
# The data is not completely symmetric so we list each route explicitly.
travel_times = {
    "Union Square": {
        "Nob Hill": 9,
        "Haight-Ashbury": 18,
        "Chinatown": 7,
        "Marina District": 18
    },
    "Nob Hill": {
        "Union Square": 7,
        "Haight-Ashbury": 13,
        "Chinatown": 6,
        "Marina District": 11
    },
    "Haight-Ashbury": {
        "Union Square": 17,
        "Nob Hill": 15,
        "Chinatown": 19,
        "Marina District": 17
    },
    "Chinatown": {
        "Union Square": 7,
        "Nob Hill": 8,
        "Haight-Ashbury": 19,
        "Marina District": 12
    },
    "Marina District": {
        "Union Square": 16,
        "Nob Hill": 12,
        "Haight-Ashbury": 16,
        "Chinatown": 16
    }
}

# Starting conditions
start_location = "Union Square"
start_time = time_to_minutes("9:00")

# We'll iterate over all permutations of friends to see which order yields a feasible schedule.
def simulate_schedule(order):
    itinerary = []
    current_time = start_time
    current_location = start_location

    for friend in order:
        friend_info = friends[friend]
        target_location = friend_info["location"]
        # Get travel time from current location to friend's location
        if current_location not in travel_times or target_location not in travel_times[current_location]:
            # if no travel time defined, schedule invalid
            return None
        travel = travel_times[current_location][target_location]
        arrival_time = current_time + travel
        
        # Wait until friend's availability start if arriving early
        meeting_start = max(arrival_time, friend_info["available_start"])
        meeting_end = meeting_start + friend_info["min_duration"]
        # Check if meeting can finish before friend's available_end
        if meeting_end > friend_info["available_end"]:
            return None  # schedule not possible
        # Record meeting event
        itinerary.append({
            "action": "meet",
            "location": target_location,
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        # Update current time and location for next leg
        current_time = meeting_end
        current_location = target_location
    return itinerary

best_itinerary = None
best_count = 0
best_end_time = 24 * 60  # large number in minutes

# Permutations of friend orders.
all_friends = list(friends.keys())
for perm in itertools.permutations(all_friends):
    schedule = simulate_schedule(perm)
    if schedule is not None:
        count = len(schedule)
        # End time of schedule is the meeting_end of the last event
        last_event = schedule[-1]
        end_time = time_to_minutes(last_event["end_time"])
        # We aim to maximize count (meet as many friends as possible) and then finish as early as possible.
        if count > best_count or (count == best_count and end_time < best_end_time):
            best_count = count
            best_end_time = end_time
            best_itinerary = schedule

# If no complete schedule found, best_itinerary could be None. Otherwise, output best_itinerary.
result = {"itinerary": best_itinerary if best_itinerary is not None else []}
print(json.dumps(result, indent=2))