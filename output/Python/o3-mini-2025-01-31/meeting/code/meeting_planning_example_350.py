#!/usr/bin/env python3
import json
import itertools

# Helper functions to convert between "H:MM" string and minutes from midnight.
def time_to_minutes(tstr):
    # tstr is in format "H:MM" (e.g., "9:00" or "13:30")
    parts = tstr.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs}:{mins:02d}"

# Define travel times in minutes as a dictionary with keys: (from, to)
travel_times = {
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Financial District"): 19,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Financial District"): 13,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Financial District"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Haight-Ashbury"): 19,
}

# Define the friend meeting constraints.
# Each friend is represented as a dictionary.
# Available times are stored as minutes from midnight.
friends = [
    {
        "name": "Mary",
        "location": "Pacific Heights",
        "available_start": time_to_minutes("10:00"),
        "available_end": time_to_minutes("19:00"),
        "min_duration": 45
    },
    {
        "name": "Lisa",
        "location": "Mission District",
        "available_start": time_to_minutes("20:30"),
        "available_end": time_to_minutes("22:00"),
        "min_duration": 75
    },
    {
        "name": "Betty",
        "location": "Haight-Ashbury",
        "available_start": time_to_minutes("7:15"),
        "available_end": time_to_minutes("17:15"),
        "min_duration": 90
    },
    {
        "name": "Charles",
        "location": "Financial District",
        "available_start": time_to_minutes("11:15"),
        "available_end": time_to_minutes("15:00"),
        "min_duration": 120
    }
]

# Starting parameters
start_location = "Bayview"
start_time = time_to_minutes("9:00")

# Given a sequence (permutation) of friends, simulate the day schedule.
def simulate_schedule(friend_sequence):
    itinerary = []
    current_time = start_time
    current_location = start_location
    
    for friend in friend_sequence:
        # Get travel time from current location to friend's location:
        if (current_location, friend["location"]) in travel_times:
            travel = travel_times[(current_location, friend["location"])]
        else:
            # If missing, consider symmetric travel time (use reverse) or skip.
            travel = travel_times.get((friend["location"], current_location), None)
            if travel is None:
                return None  # invalid travel info
        arrival_time = current_time + travel
        # Determine meeting start time by waiting if needed.
        meeting_start = max(arrival_time, friend["available_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if meeting can finish before friend's availability ends.
        if meeting_end > friend["available_end"]:
            return None  # schedule not possible with this ordering.
        # Append meeting event to itinerary.
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        # Update the current time and location.
        current_time = meeting_end
        current_location = friend["location"]
    return itinerary

# We want to maximize the number of meetings. We try all permutations.
best_itinerary = None
max_meetings = 0

for r in range(len(friends), 0, -1):
    # Try all combinations of r friends in order.
    for subset in itertools.permutations(friends, r):
        schedule = simulate_schedule(subset)
        if schedule is not None:
            if r > max_meetings:
                max_meetings = r
                best_itinerary = schedule
    # If we found an itinerary with all r meetings, break out.
    if best_itinerary is not None:
        break

# If a best itinerary is found, output it, otherwise output an empty itinerary.
result = {"itinerary": best_itinerary if best_itinerary is not None else []}

print(json.dumps(result))