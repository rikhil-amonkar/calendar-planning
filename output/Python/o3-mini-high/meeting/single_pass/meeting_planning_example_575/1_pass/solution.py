#!/usr/bin/env python3
import itertools
import json

def time_to_str(t):
    hr = t // 60
    mn = t % 60
    return f"{hr}:{mn:02d}"

# Define travel times between locations (in minutes)
travel_times = {
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Russian Hill"): 18,
    
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Russian Hill"): 14,
    
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Russian Hill"): 24,
    
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Russian Hill"): 17,
    
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Russian Hill"): 15,
    
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Russian Hill"): 19,
    
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Golden Gate Park"): 21
}

# Meeting constraints for each friend:
# Each friend has a fixed location, an availability window (start and end times in minutes after midnight),
# and a minimum meeting duration (in minutes).
meetings = {
    "Rebecca": {
        "location": "Presidio",
        "available_start": 18 * 60 + 15,  # 18:15 -> 1095 minutes
        "available_end": 20 * 60 + 45,      # 20:45 -> 1245 minutes
        "duration": 60
    },
    "Linda": {
        "location": "Sunset District",
        "available_start": 15 * 60 + 30,  # 15:30 -> 930 minutes
        "available_end": 19 * 60 + 45,      # 19:45 -> 1185 minutes
        "duration": 30
    },
    "Elizabeth": {
        "location": "Haight-Ashbury",
        "available_start": 17 * 60 + 15,  # 17:15 -> 1035 minutes
        "available_end": 19 * 60 + 30,      # 19:30 -> 1170 minutes
        "duration": 105
    },
    "William": {
        "location": "Mission District",
        "available_start": 13 * 60 + 15,  # 13:15 -> 795 minutes
        "available_end": 19 * 60 + 30,      # 19:30 -> 1170 minutes
        "duration": 30
    },
    "Robert": {
        "location": "Golden Gate Park",
        "available_start": 14 * 60 + 15,  # 14:15 -> 855 minutes
        "available_end": 21 * 60 + 30,      # 21:30 -> 1290 minutes
        "duration": 45
    },
    "Mark": {
        "location": "Russian Hill",
        "available_start": 10 * 60,       # 10:00 -> 600 minutes
        "available_end": 21 * 60 + 15,      # 21:15 -> 1275 minutes
        "duration": 75
    }
}

# List of friends to consider
persons = list(meetings.keys())

best_schedule = None
best_count = -1
best_finish_time = float('inf')

# Iterate over all possible orders (permutations) of meeting friends
for perm in itertools.permutations(persons):
    # Start at The Castro at 9:00AM (540 minutes)
    current_time = 9 * 60
    current_location = "The Castro"
    itinerary = []
    count = 0

    for person in perm:
        friend = meetings[person]
        destination = friend["location"]
        # Get travel time from current location to friend's location
        travel = travel_times.get((current_location, destination))
        if travel is None:
            break  # if no travel info is available, skip this permutation

        arrival_time = current_time + travel
        meeting_start = max(arrival_time, friend["available_start"])
        meeting_end = meeting_start + friend["duration"]

        # Check if the meeting can finish before the friend leaves
        if meeting_end <= friend["available_end"]:
            itinerary.append({
                "action": "meet",
                "location": destination,
                "person": person,
                "start_time": time_to_str(meeting_start),
                "end_time": time_to_str(meeting_end)
            })
            count += 1
            current_time = meeting_end
            current_location = destination
        else:
            break  # meeting cannot be scheduled, so end this permutation's simulation

    # Choose the best itinerary by the maximum number of meetings, using finish time as tie-breaker
    if count > best_count or (count == best_count and current_time < best_finish_time):
        best_count = count
        best_finish_time = current_time
        best_schedule = itinerary

result = {"itinerary": best_schedule if best_schedule is not None else []}
print(json.dumps(result))