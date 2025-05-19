#!/usr/bin/env python3
import json
import itertools

# Helper functions for time conversion
def time_to_minutes(time_str):
    # expects "H:MM" format (24-hour)
    h, m = time_str.split(":")
    return int(h) * 60 + int(m)

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define travel times between locations as a dictionary
# Keys are (from, to) with travel time in minutes.
travel_times = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
}

# Define friend meeting constraints as dictionaries
# Each friend's available time window and meeting duration are stored in minutes (from midnight).
friends = [
    {
        "name": "Stephanie",
        "location": "Mission District",
        "avail_start": time_to_minutes("8:15"),
        "avail_end": time_to_minutes("13:45"),
        "duration": 90
    },
    {
        "name": "Sandra",
        "location": "Bayview",
        "avail_start": time_to_minutes("13:00"),
        "avail_end": time_to_minutes("19:30"),
        "duration": 15
    },
    {
        "name": "Richard",
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("7:15"),
        "avail_end": time_to_minutes("10:15"),
        "duration": 75
    },
    {
        "name": "Brian",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("12:15"),
        "avail_end": time_to_minutes("16:00"),
        "duration": 120
    },
    {
        "name": "Jason",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("8:30"),
        "avail_end": time_to_minutes("17:45"),
        "duration": 60
    }
]

# Starting point details
start_location = "Haight-Ashbury"
start_time = time_to_minutes("9:00")  # 9:00 in minutes

# Function to simulate a given itinerary permutation.
# It returns the itinerary (list of meetings) and count of meetings if feasible;
# Otherwise it returns None.
def simulate_itinerary(order):
    itinerary = []
    current_time = start_time
    current_location = start_location
    for friend in order:
        # Get travel time from current location to friend's location.
        travel_key = (current_location, friend["location"])
        if travel_key not in travel_times:
            # If no defined travel time then skip this itinerary.
            return None
        travel_time = travel_times[travel_key]
        arrival_time = current_time + travel_time
        
        # Meeting can only start when friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        
        # Check if meeting fits within friend's available window.
        if meeting_end > friend["avail_end"]:
            # Cannot meet friend within available window, so this itinerary is not feasible.
            return None
        
        # Append meeting details to the itinerary.
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update current time and location after meeting.
        current_time = meeting_end
        current_location = friend["location"]
    return itinerary

# Try all permutations of friends to maximize the number of meetings.
# Our goal is to meet as many friends as possible.
best_itinerary = None
max_count = 0

# We'll also check for partial itineraries by trying subsets of friends.
# We'll iterate over all combinations (of all lengths) and their orders.
for r in range(1, len(friends)+1):
    for subset in itertools.permutations(friends, r):
        res = simulate_itinerary(subset)
        if res is not None:
            if r > max_count:
                max_count = r
                best_itinerary = res

# Prepare the result dictionary in the required format.
result = {"itinerary": best_itinerary if best_itinerary is not None else []}

# Output the result as JSON
print(json.dumps(result, indent=2))