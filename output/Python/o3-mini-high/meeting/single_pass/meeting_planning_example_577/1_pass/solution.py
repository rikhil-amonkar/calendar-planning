#!/usr/bin/env python3
import json

# Utility functions to convert time strings to minutes and back.
def time_to_minutes(t):
    # t format is "H:MM" in 24-hour time (e.g., "9:00" or "20:45")
    parts = t.split(":")
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) between locations
# The keys are location names exactly as given.
travel_times = {
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
        "Nob Hill": 15,
        "Golden Gate Park": 7,
        "Alamo Square": 5,
        "Pacific Heights": 12,
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Nob Hill": 5,
        "Golden Gate Park": 21,
        "Alamo Square": 15,
        "Pacific Heights": 7,
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Alamo Square": 20,
        "Pacific Heights": 12,
    },
    "Nob Hill": {
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "Fisherman's Wharf": 11,
        "Golden Gate Park": 17,
        "Alamo Square": 11,
        "Pacific Heights": 8,
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Russian Hill": 19,
        "Fisherman's Wharf": 24,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "Pacific Heights": 16,
    },
    "Alamo Square": {
        "Haight-Ashbury": 5,
        "Russian Hill": 13,
        "Fisherman's Wharf": 19,
        "Nob Hill": 11,
        "Golden Gate Park": 9,
        "Pacific Heights": 10,
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
        "Nob Hill": 8,
        "Golden Gate Park": 15,
        "Alamo Square": 10,
    }
}

# Define the friends' meeting constraints.
# Each friend is defined with:
# - location: where they are
# - avail_start: when they are available (in minutes from midnight)
# - avail_end: until when they are available (in minutes)
# - duration: minimum meeting duration (in minutes)
friends_info = {
    "Stephanie": {
        "location": "Russian Hill",
        "avail_start": time_to_minutes("20:00"),
        "avail_end": time_to_minutes("20:45"),
        "duration": 15
    },
    "Kevin": {
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("19:15"),
        "avail_end": time_to_minutes("21:45"),
        "duration": 75
    },
    "Robert": {
        "location": "Nob Hill",
        "avail_start": time_to_minutes("7:45"),
        "avail_end": time_to_minutes("10:30"),
        "duration": 90
    },
    "Steven": {
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("8:30"),
        "avail_end": time_to_minutes("17:00"),
        "duration": 75
    },
    "Anthony": {
        "location": "Alamo Square",
        "avail_start": time_to_minutes("7:45"),
        "avail_end": time_to_minutes("19:45"),
        "duration": 15
    },
    "Sandra": {
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("21:45"),
        "duration": 45
    }
}

# Our starting state: we arrive at Haight-Ashbury at 9:00AM.
start_location = "Haight-Ashbury"
start_time = time_to_minutes("9:00")

# We'll use DFS/backtracking to try to schedule meetings in different orders,
# aiming to maximize the number of friends met.
def dfs(curr_loc, curr_time, remaining, itinerary):
    best_itinerary = list(itinerary)
    # Try each friend in the remaining list
    for friend in remaining:
        friend_data = friends_info[friend]
        destination = friend_data["location"]
        # Check travel time from current location to friend's location.
        travel = travel_times[curr_loc][destination]
        arrival_time = curr_time + travel
        # The meeting can only start when we both have arrived and friend is available.
        meeting_start = max(arrival_time, friend_data["avail_start"])
        meeting_end = meeting_start + friend_data["duration"]
        # Check if the meeting can end before the friend's availability window closes.
        if meeting_end <= friend_data["avail_end"]:
            meeting_event = {
                "action": "meet",
                "location": destination,
                "person": friend,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_itinerary = itinerary + [meeting_event]
            new_remaining = remaining.copy()
            new_remaining.remove(friend)
            candidate = dfs(destination, meeting_end, new_remaining, new_itinerary)
            if len(candidate) > len(best_itinerary):
                best_itinerary = candidate
    return best_itinerary

def main():
    # List of all friends (keys of friends_info)
    friends_list = list(friends_info.keys())
    best_schedule = dfs(start_location, start_time, friends_list, [])
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))
    
if __name__ == '__main__':
    main()