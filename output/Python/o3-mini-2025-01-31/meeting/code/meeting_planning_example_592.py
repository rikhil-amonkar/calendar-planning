#!/usr/bin/env python3
import json
import itertools

# Helper: format minutes since midnight to H:MM (24-hour, no leading zero for hours)
def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes as provided
travel_times = {
    "North Beach": {
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 22,
        "Nob Hill": 7,
    },
    "Pacific Heights": {
        "North Beach": 9,
        "Chinatown": 11,
        "Union Square": 12,
        "Mission District": 15,
        "Golden Gate Park": 15,
        "Nob Hill": 8,
    },
    "Chinatown": {
        "North Beach": 3,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 23,
        "Nob Hill": 8,
    },
    "Union Square": {
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Mission District": 14,
        "Golden Gate Park": 22,
        "Nob Hill": 9,
    },
    "Mission District": {
        "North Beach": 17,
        "Pacific Heights": 16,
        "Chinatown": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Nob Hill": 12,
    },
    "Golden Gate Park": {
        "North Beach": 24,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Union Square": 22,
        "Mission District": 17,
        "Nob Hill": 20,
    },
    "Nob Hill": {
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 13,
        "Golden Gate Park": 17,
    },
}

# Meeting constraints for each friend
# Times are in minutes from midnight.
meetings = {
    "James": {
        "location": "Pacific Heights",
        "available_start": 20 * 60,    # 20:00 -> 1200
        "available_end": 22 * 60,      # 22:00 -> 1320
        "min_duration": 120,
    },
    "Robert": {
        "location": "Chinatown",
        "available_start": 12 * 60 + 15,  # 12:15 -> 735
        "available_end": 16 * 60 + 45,      # 16:45 -> 1005
        "min_duration": 90,
    },
    "Jeffrey": {
        "location": "Union Square",
        "available_start": 9 * 60 + 30,   # 9:30 -> 570
        "available_end": 15 * 60 + 30,      # 15:30 -> 930
        "min_duration": 120,
    },
    "Carol": {
        "location": "Mission District",
        "available_start": 18 * 60 + 15,   # 18:15 -> 1095
        "available_end": 21 * 60 + 15,      # 21:15 -> 1275
        "min_duration": 15,
    },
    "Mark": {
        "location": "Golden Gate Park",
        "available_start": 11 * 60 + 30,  # 11:30 -> 690
        "available_end": 17 * 60 + 45,      # 17:45 -> 1065
        "min_duration": 15,
    },
    "Sandra": {
        "location": "Nob Hill",
        "available_start": 8 * 60,       # 8:00 -> 480
        "available_end": 15 * 60 + 30,      # 15:30 -> 930
        "min_duration": 15,
    },
}

# Starting conditions
start_location = "North Beach"
start_time = 9 * 60  # 9:00 -> 540 minutes

# Function to get travel time between two locations
def get_travel_time(from_loc, to_loc):
    # travel_times dict might not be symmetric; use provided value from from_loc to to_loc.
    return travel_times[from_loc][to_loc]

# Simulate an itinerary given an order of meeting names.
# Returns a tuple (itinerary_list, finish_time) if feasible, otherwise (None, None)
def simulate_itinerary(order):
    itinerary = []
    current_time = start_time
    current_location = start_location
    for person in order:
        m = meetings[person]
        meeting_location = m["location"]

        # Get travel time from current location to meeting location
        travel = get_travel_time(current_location, meeting_location)
        arrival_time = current_time + travel

        # Determine meeting start: cannot start before available_start.
        meeting_start = max(arrival_time, m["available_start"])
        meeting_end = meeting_start + m["min_duration"]

        # Check if meeting can finish before available_end.
        if meeting_end > m["available_end"]:
            return None, None

        itinerary.append({
            "action": "meet",
            "location": meeting_location,
            "person": person,
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end),
        })

        # Update current time and location.
        current_time = meeting_end
        current_location = meeting_location

    return itinerary, current_time

# We want to choose the itinerary that meets the maximum number of friends.
# Since there are only 6 friends, we try all possible orders.
best_itinerary = None
max_meetings = 0
best_end_time = None

friends = list(meetings.keys())
# Consider all permutations of friends.
for order in itertools.permutations(friends):
    itinerary, finish_time = simulate_itinerary(order)
    if itinerary is not None:
        count = len(itinerary)
        # For optimization, if same count choose the one with earliest finish_time.
        if count > max_meetings or (count == max_meetings and (best_end_time is None or finish_time < best_end_time)):
            max_meetings = count
            best_itinerary = itinerary
            best_end_time = finish_time

# If no itinerary is found, return an empty itinerary.
if best_itinerary is None:
    result = {"itinerary": []}
else:
    result = {"itinerary": best_itinerary}

# Output the result as JSON.
print(json.dumps(result, indent=2))
    
if __name__ == "__main__":
    pass