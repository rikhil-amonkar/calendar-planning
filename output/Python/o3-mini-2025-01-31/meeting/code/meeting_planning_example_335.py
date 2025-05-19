#!/usr/bin/env python3
import json
import itertools

# Helper functions to convert between "H:MM" strings and minutes from midnight.
def time_to_minutes(t):
    # t is a string like "9:00" or "13:30"
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    # return hour without leading zero, minute with two digits if needed
    return f"{h}:{mm:02d}"

# Define travel times in minutes in a dictionary for directional travel.
travel_times = {
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Mission District"): 15,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Mission District"): 18,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Alamo Square"): 11
}

# Friends meeting constraints: each friend has:
# name, location, available_start, available_end, required_meeting_duration (in minutes)
friends = [
    {
        "name": "Helen",
        "location": "North Beach",
        "available_start": time_to_minutes("9:00"),
        "available_end": time_to_minutes("17:00"),
        "meeting_duration": 15
    },
    {
        "name": "Betty",
        "location": "Financial District",
        "available_start": time_to_minutes("19:00"),
        "available_end": time_to_minutes("21:45"),
        "meeting_duration": 90
    },
    {
        "name": "Amanda",
        "location": "Alamo Square",
        "available_start": time_to_minutes("19:45"),
        "available_end": time_to_minutes("21:00"),
        "meeting_duration": 60
    },
    {
        "name": "Kevin",
        "location": "Mission District",
        "available_start": time_to_minutes("10:45"),
        "available_end": time_to_minutes("14:45"),
        "meeting_duration": 45
    }
]

# Starting point and time
start_location = "Pacific Heights"
start_time = time_to_minutes("9:00")

# Evaluate a given schedule (list of friend dictionaries in order) 
# Returns: None if schedule is not feasible, otherwise a tuple (finish_time, itinerary)
def evaluate_schedule(schedule):
    current_time = start_time
    current_location = start_location
    itinerary = []
    
    for friend in schedule:
        # travel from current location to friend's location
        # if same location (should not occur in our case) then travel time is 0.
        travel = travel_times.get((current_location, friend["location"]), None)
        if travel is None:
            # If no defined travel time, skip this schedule.
            return None
        arrival_time = current_time + travel
        
        # Wait until friend's available start if arrived earlier.
        meeting_start = max(arrival_time, friend["available_start"])
        meeting_end = meeting_start + friend["meeting_duration"]
        
        # Check if meeting can finish before friend's available end.
        if meeting_end > friend["available_end"]:
            return None
        
        # Append meeting event to itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = friend["location"]
    
    return (current_time, itinerary)

# We want to maximize the number of meetings (friends met)
# We'll try all possible orders of any subset of friends.
best_itinerary = None
max_meetings = 0
best_finish_time = None

# Generate all subsets (of lengths 1 to all) and all permutations of each subset.
n = len(friends)
for r in range(1, n+1):
    for subset in itertools.permutations(friends, r):
        result = evaluate_schedule(subset)
        if result is not None:
            finish_time, itinerary = result
            num_meetings = len(itinerary)
            if num_meetings > max_meetings:
                max_meetings = num_meetings
                best_itinerary = itinerary
                best_finish_time = finish_time
            elif num_meetings == max_meetings:
                # if same number of meetings, choose the one finishing earlier
                if finish_time < best_finish_time:
                    best_itinerary = itinerary
                    best_finish_time = finish_time

# Prepare output dictionary in required JSON format.
output = {"itinerary": best_itinerary if best_itinerary is not None else []}

# Print the JSON output.
print(json.dumps(output, indent=2))
                    
if __name__ == '__main__':
    pass