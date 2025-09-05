#!/usr/bin/env python3
import itertools
import json

# Define travel times (in minutes) between locations.
travel_times = {
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Mission District": 17,
        "Embarcadero": 25,
        "Financial District": 26
    },
    "Fisherman's Wharf": {
        "Golden Gate Park": 25,
        "Bayview": 26,
        "Mission District": 22,
        "Embarcadero": 8,
        "Financial District": 11
    },
    "Bayview": {
        "Golden Gate Park": 22,
        "Fisherman's Wharf": 25,
        "Mission District": 13,
        "Embarcadero": 19,
        "Financial District": 19
    },
    "Mission District": {
        "Golden Gate Park": 17,
        "Fisherman's Wharf": 22,
        "Bayview": 15,
        "Embarcadero": 19,
        "Financial District": 17
    },
    "Embarcadero": {
        "Golden Gate Park": 25,
        "Fisherman's Wharf": 6,
        "Bayview": 21,
        "Mission District": 20,
        "Financial District": 5
    },
    "Financial District": {
        "Golden Gate Park": 23,
        "Fisherman's Wharf": 10,
        "Bayview": 19,
        "Mission District": 17,
        "Embarcadero": 4
    }
}

# Define meeting constraints for each friend.
# Times are represented in minutes since midnight.
meetings = [
    {
        "person": "Joseph",
        "location": "Fisherman's Wharf",
        "avail_start": 8 * 60 + 0,      # 8:00
        "avail_end": 17 * 60 + 30,      # 17:30
        "duration": 90                # 90 minutes required
    },
    {
        "person": "Jeffrey",
        "location": "Bayview",
        "avail_start": 17 * 60 + 30,    # 17:30
        "avail_end": 21 * 60 + 30,      # 21:30
        "duration": 60                # 60 minutes required
    },
    {
        "person": "Kevin",
        "location": "Mission District",
        "avail_start": 11 * 60 + 15,    # 11:15
        "avail_end": 15 * 60 + 15,      # 15:15
        "duration": 30                # 30 minutes required
    },
    {
        "person": "David",
        "location": "Embarcadero",
        "avail_start": 8 * 60 + 15,     # 8:15
        "avail_end": 9 * 60 + 0,        # 9:00
        "duration": 30                # 30 minutes required
    },
    {
        "person": "Barbara",
        "location": "Financial District",
        "avail_start": 10 * 60 + 30,    # 10:30
        "avail_end": 16 * 60 + 30,      # 16:30
        "duration": 15                # 15 minutes required
    }
]

# Starting conditions
start_location = "Golden Gate Park"
start_time = 9 * 60   # 9:00 in minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to H:MM 24-hour time format (no leading zero for hour)."""
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# We'll search for the schedule (itinerary) that meets the maximum number of friends.
# If multiple itineraries yield the same count, choose the one that finishes earliest.
best_itinerary = None
best_finish_time = float('inf')
best_count = 0

# Generate all possible subsets of meetings in descending order of size.
n = len(meetings)
# Try all combinations of r meetings, starting with the largest possible r.
for r in range(n, 0, -1):
    found_feasible = False
    # combinations returns tuples of r meetings (order not considered yet)
    for combo in itertools.combinations(meetings, r):
        # For each combination, try every possible order (permutation).
        for perm in itertools.permutations(combo):
            current_time = start_time
            current_location = start_location
            itinerary = []
            feasible = True
            
            for meeting in perm:
                # Calculate travel time from the current location to the next meeting location.
                travel_time = travel_times[current_location][meeting["location"]]
                arrival_time = current_time + travel_time
                # The meeting can only start once the friend is available.
                meeting_start = max(arrival_time, meeting["avail_start"])
                meeting_end = meeting_start + meeting["duration"]
                
                # Check if this meeting can be completed within the friend's available window.
                if meeting_end > meeting["avail_end"]:
                    feasible = False
                    break
                
                # Record the meeting in the itinerary.
                itinerary.append({
                    "action": "meet",
                    "location": meeting["location"],
                    "person": meeting["person"],
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                })
                # Update current time and location for the next meeting.
                current_time = meeting_end
                current_location = meeting["location"]
            
            if feasible:
                found_feasible = True
                # Update best itinerary if more meetings or if the finish time is earlier.
                if r > best_count or (r == best_count and current_time < best_finish_time):
                    best_count = r
                    best_finish_time = current_time
                    best_itinerary = itinerary
    if found_feasible:
        # We found the itinerary with the maximum number of meetings for this subset size.
        break

# Prepare the final output dictionary.
output = {
    "itinerary": best_itinerary if best_itinerary is not None else []
}

# Print the result as a JSON-formatted string.
print(json.dumps(output, indent=2))