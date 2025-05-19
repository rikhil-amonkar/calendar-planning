#!/usr/bin/env python3
import json
import itertools

def time_to_minutes(time_str):
    # time_str in format "H:MM" or "HH:MM"
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel time matrix (in minutes) as a dictionary
# Key is (from, to)
travel_times = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Fisherman's Wharf"): 10,
    
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Fisherman's Wharf"): 8,
    
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
    
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Bayview"): 26,
}

# Meeting constraints data: each friend with their meeting location, available window, and required meeting duration (in minutes)
# Times are in 24-hour format as strings.
friends = {
    "Nancy": {
        "location": "Chinatown",
        "avail_start": time_to_minutes("9:30"),
        "avail_end": time_to_minutes("13:30"),
        "duration": 90
    },
    "Mary": {
        "location": "Alamo Square",
        "avail_start": time_to_minutes("7:00"),
        "avail_end": time_to_minutes("21:00"),
        "duration": 75
    },
    "Jessica": {
        "location": "Bayview",
        "avail_start": time_to_minutes("11:15"),
        "avail_end": time_to_minutes("13:45"),
        "duration": 45
    },
    "Rebecca": {
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("7:00"),
        "avail_end": time_to_minutes("8:30"),
        "duration": 45
    }
}

# Starting location and start time
start_location = "Financial District"
start_time = time_to_minutes("9:00")

def is_schedule_feasible(order):
    """
    Given an order (list of friend names), simulate the day's schedule.
    Returns the itinerary (list of meeting events) if feasible, else None.
    Each event is a dictionary containing:
      action, location, person, start_time, end_time.
    """
    itinerary = []
    current_location = start_location
    current_time = start_time

    for friend in order:
        friend_info = friends[friend]
        meeting_location = friend_info["location"]
        # if current_location equals meeting_location, travel time is 0, else get travel time
        travel_time = travel_times.get((current_location, meeting_location), None)
        if travel_time is None:
            # if no direct road, skip schedule 
            return None
        # travel from current location to meeting location
        current_time += travel_time
        # Wait if arrived before friend's available start time
        meeting_start = max(current_time, friend_info["avail_start"])
        meeting_end = meeting_start + friend_info["duration"]
        # Check if meeting finishes within friend's available window
        if meeting_end > friend_info["avail_end"]:
            return None
        # Append meeting event to itinerary
        event = {
            "action": "meet",
            "location": meeting_location,
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        itinerary.append(event)
        # Update current time and position
        current_time = meeting_end
        current_location = meeting_location
    return itinerary

# We want to maximize the number of friends met.
# Try all permutations of friends.
best_itinerary = None
max_meetings = 0

# Evaluate each subset of friends (not necessarily all four) in all orders.
# We'll try orders of length k for k=1,...,number of friends.
all_friend_names = list(friends.keys())
for k in range(1, len(all_friend_names) + 1):
    for subset in itertools.permutations(all_friend_names, k):
        itinerary = is_schedule_feasible(subset)
        if itinerary is not None:
            if k > max_meetings:
                max_meetings = k
                best_itinerary = itinerary
            # If same count, we can choose the one that finishes earlier
            elif k == max_meetings:
                # Compare finishing times (last meeting's end time in minutes)
                current_finish = time_to_minutes(itinerary[-1]["end_time"])
                best_finish = time_to_minutes(best_itinerary[-1]["end_time"])
                if current_finish < best_finish:
                    best_itinerary = itinerary

# For our problem, we want to meet as many friends as possible.
# We assume that the solution is the one with maximum meetings.
result = {"itinerary": best_itinerary if best_itinerary is not None else []}

print(json.dumps(result, indent=2))