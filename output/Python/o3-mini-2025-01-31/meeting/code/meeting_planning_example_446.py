#!/usr/bin/env python3
import itertools
import json

# Helper functions to convert between time strings and minutes since midnight.
def time_to_minutes(timestr):
    # timestr format "H:MM" e.g., "9:00" or "13:15"
    parts = timestr.split(":")
    return int(parts[0]) * 60 + int(parts[1])
    
def minutes_to_timestr(minutes):
    h = minutes // 60
    m = minutes % 60
    # Format as H:MM with no leading zero for hour.
    return f"{h}:{m:02d}"

# Define travel times in minutes between districts.
# Each key is the origin location and value is a dict mapping destination to travel minutes.
travel_times = {
    "Richmond District": {
        "Marina District": 9,
        "Chinatown": 20,
        "Financial District": 22,
        "Bayview": 26,
        "Union Square": 21
    },
    "Marina District": {
        "Richmond District": 11,
        "Chinatown": 16,
        "Financial District": 17,
        "Bayview": 27,
        "Union Square": 16
    },
    "Chinatown": {
        "Richmond District": 20,
        "Marina District": 12,
        "Financial District": 5,
        "Bayview": 22,
        "Union Square": 7
    },
    "Financial District": {
        "Richmond District": 21,
        "Marina District": 15,
        "Chinatown": 5,
        "Bayview": 19,
        "Union Square": 9
    },
    "Bayview": {
        "Richmond District": 25,
        "Marina District": 25,
        "Chinatown": 18,
        "Financial District": 19,
        "Union Square": 17
    },
    "Union Square": {
        "Richmond District": 20,
        "Marina District": 18,
        "Chinatown": 7,
        "Financial District": 9,
        "Bayview": 15
    }
}

# Define meeting constraints for each friend.
# Each meeting includes:
#   name: Friend's name
#   location: Where to meet
#   window_start, window_end: availability window in minutes since midnight
#   duration: minimum meeting duration in minutes.
friends = [
    {
        "name": "Kimberly",
        "location": "Marina District",
        "window_start": time_to_minutes("13:15"),
        "window_end": time_to_minutes("16:45"),
        "duration": 15
    },
    {
        "name": "Robert",
        "location": "Chinatown",
        "window_start": time_to_minutes("12:15"),
        "window_end": time_to_minutes("20:15"),
        "duration": 15
    },
    {
        "name": "Rebecca",
        "location": "Financial District",
        "window_start": time_to_minutes("13:15"),
        "window_end": time_to_minutes("16:45"),
        "duration": 75
    },
    {
        "name": "Margaret",
        "location": "Bayview",
        "window_start": time_to_minutes("9:30"),
        "window_end": time_to_minutes("13:30"),
        "duration": 30
    },
    {
        "name": "Kenneth",
        "location": "Union Square",
        "window_start": time_to_minutes("19:30"),
        "window_end": time_to_minutes("21:15"),
        "duration": 75
    }
]

# Starting conditions: you arrive at Richmond District at 9:00AM.
start_location = "Richmond District"
start_time = time_to_minutes("9:00")

# Function to evaluate a given ordering (permutation) of meetings.
# It returns a tuple (number_of_meetings, finish_time, itinerary) if the schedule is feasible,
# or (number_of_meetings, float('inf'), itinerary) if meeting count is lower.
def evaluate_schedule(order):
    itinerary = []
    current_time = start_time
    current_location = start_location
    meetings_met = 0
    
    for friend in order:
        # Travel from current_location to friend's meeting location.
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        
        # The meeting can't start before the friend's window opens.
        meeting_start = max(arrival_time, friend["window_start"])
        meeting_end = meeting_start + friend["duration"]
        
        # Check if the meeting can be completed before the friend's window closes.
        if meeting_end > friend["window_end"]:
            # Cannot meet this friend in this order; return count so far.
            return meetings_met, float('inf'), itinerary
        
        # Add meeting to the itinerary.
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_timestr(meeting_start),
            "end_time": minutes_to_timestr(meeting_end)
        })
        
        # Update current time and location.
        current_time = meeting_end
        current_location = friend["location"]
        meetings_met += 1
        
    return meetings_met, current_time, itinerary

# Try all permutations to maximize the number of meetings.
best_itinerary = None
max_meetings = 0
best_finish_time = float('inf')

for order in itertools.permutations(friends):
    met, finish, itinerary = evaluate_schedule(order)
    if met > max_meetings or (met == max_meetings and finish < best_finish_time):
        max_meetings = met
        best_finish_time = finish
        best_itinerary = itinerary

# Prepare final output dictionary.
output = {"itinerary": best_itinerary if best_itinerary is not None else []}

# Print the output as JSON.
print(json.dumps(output, indent=2))
    
if __name__ == "__main__":
    pass