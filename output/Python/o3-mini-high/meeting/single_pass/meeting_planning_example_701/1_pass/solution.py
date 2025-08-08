#!/usr/bin/env python3
import json

# Convert minutes (integer) to "H:MM" string (24‐hour format, no leading zero for hour)
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define travel times between locations (in minutes) as provided.
travel_times = {
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Richmond District"): 20,

    ("The Castro", "Mission District"): 7,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Richmond District"): 16,

    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Richmond District"): 14,

    ("Presidio", "Mission District"): 26,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Richmond District"): 7,

    ("Marina District", "Mission District"): 20,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Richmond District"): 11,

    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,

    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,

    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Richmond District"): 20,

    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Chinatown"): 20
}

# Define meeting constraints for each friend.
# Times are converted to minutes after midnight.
# Note: "9:00" AM is 9*60 = 540.
# For times in the afternoon/evening, e.g., 7:15PM is 19:15 (i.e. 1155 minutes)
meetings = [
    {
        "person": "Lisa",
        "location": "The Castro",
        "avail_start": 19 * 60 + 15,  # 19:15 -> 1155
        "avail_end": 21 * 60 + 15,    # 21:15 -> 1275
        "duration": 120
    },
    {
        "person": "Daniel",
        "location": "Nob Hill",
        "avail_start": 8 * 60 + 15,   # 8:15 -> 495
        "avail_end": 11 * 60,         # 11:00 -> 660
        "duration": 15
    },
    {
        "person": "Elizabeth",
        "location": "Presidio",
        "avail_start": 21 * 60 + 15,  # 21:15 -> 1275
        "avail_end": 22 * 60 + 15,    # 22:15 -> 1335
        "duration": 45
    },
    {
        "person": "Steven",
        "location": "Marina District",
        "avail_start": 16 * 60 + 30,  # 16:30 -> 990
        "avail_end": 20 * 60 + 45,    # 20:45 -> 1245
        "duration": 90
    },
    {
        "person": "Timothy",
        "location": "Pacific Heights",
        "avail_start": 12 * 60,       # 12:00 -> 720
        "avail_end": 18 * 60,         # 18:00 -> 1080
        "duration": 90
    },
    {
        "person": "Ashley",
        "location": "Golden Gate Park",
        "avail_start": 20 * 60 + 45,  # 20:45 -> 1245
        "avail_end": 21 * 60 + 45,    # 21:45 -> 1305
        "duration": 60
    },
    {
        "person": "Kevin",
        "location": "Chinatown",
        "avail_start": 12 * 60,       # 12:00 -> 720
        "avail_end": 19 * 60,         # 19:00 -> 1140
        "duration": 30
    },
    {
        "person": "Betty",
        "location": "Richmond District",
        "avail_start": 13 * 60 + 15,  # 13:15 -> 795
        "avail_end": 15 * 60 + 45,    # 15:45 -> 945
        "duration": 30
    }
]

# Global variable to hold the best (optimal) schedule found.
best_solution = {"count": 0, "finish_time": float('inf'), "itinerary": []}

# Recursive DFS that tries all orders (subsets) of meetings.
def dfs(current_time, current_location, remaining, itinerary):
    global best_solution
    # Update global best if current itinerary is better (more meetings, or same count with earlier finish)
    if len(itinerary) > best_solution["count"] or (len(itinerary) == best_solution["count"] and current_time < best_solution["finish_time"]):
        best_solution = {
            "count": len(itinerary),
            "finish_time": current_time,
            "itinerary": itinerary.copy()
        }
    # Try scheduling each remaining meeting in turn.
    for i in range(len(remaining)):
        meeting = remaining[i]
        # Get travel time from current location to the meeting location.
        if (current_location, meeting["location"]) not in travel_times:
            continue
        travel = travel_times[(current_location, meeting["location"])]
        arrival = current_time + travel
        # The meeting can only start when both you arrive and its availability begins.
        start_meet = max(arrival, meeting["avail_start"])
        meeting_end = start_meet + meeting["duration"]
        # Check if meeting can finish before the friend leaves.
        if meeting_end > meeting["avail_end"]:
            continue
        # Create the scheduled meeting entry.
        scheduled = {
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(start_meet),
            "end_time": minutes_to_time(meeting_end)
        }
        new_itinerary = itinerary + [scheduled]
        # Remove the meeting from the remaining list.
        new_remaining = remaining[:i] + remaining[i+1:]
        dfs(meeting_end, meeting["location"], new_remaining, new_itinerary)

# Starting condition: Arrive at Mission District at 9:00 AM (9*60 = 540 minutes)
start_time = 9 * 60  # 9:00 AM
start_location = "Mission District"

dfs(start_time, start_location, meetings, [])

# Prepare the result JSON dictionary.
result = {"itinerary": best_solution["itinerary"]}

# Output the result as a JSON formatted string.
print(json.dumps(result, indent=2))