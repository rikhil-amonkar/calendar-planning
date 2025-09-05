import json
import copy

# Convert time in minutes (from midnight) to "H:MM" 24-hour string (no leading zero for hour)
def minutes_to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel time matrix in minutes (directed)
travel_times = {
    "Financial District": {
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Pacific Heights": 13,
        "North Beach": 7,
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Chinatown": 23,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Pacific Heights": 16,
        "North Beach": 24,
    },
    "Chinatown": {
        "Financial District": 5,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Fisherman's Wharf": 8,
        "Pacific Heights": 10,
        "North Beach": 3,
    },
    "Union Square": {
        "Financial District": 9,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Fisherman's Wharf": 15,
        "Pacific Heights": 15,
        "North Beach": 10,
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Union Square": 13,
        "Pacific Heights": 12,
        "North Beach": 6,
    },
    "Pacific Heights": {
        "Financial District": 13,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "North Beach": 9,
    },
    "North Beach": {
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Chinatown": 6,
        "Union Square": 7,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8,
    }
}

# Define the friends with their meeting constraints.
# Times are in minutes after midnight.
# For example, 9:00 AM is 9*60 = 540.
friends = [
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "avail_start": 11 * 60,         # 11:00 -> 660
        "avail_end": 15 * 60,           # 15:00 -> 900
        "duration": 105
    },
    {
        "name": "Karen",
        "location": "Chinatown",
        "avail_start": 13 * 60 + 45,    # 13:45 -> 825
        "avail_end": 16 * 60 + 30,      # 16:30 -> 990
        "duration": 15
    },
    {
        "name": "Brian",
        "location": "Union Square",
        "avail_start": 15 * 60,         # 15:00 -> 900
        "avail_end": 17 * 60 + 15,      # 17:15 -> 1035
        "duration": 30
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "avail_start": 8 * 60,          # 8:00 -> 480
        "avail_end": 11 * 60 + 15,      # 11:15 -> 675
        "duration": 30
    },
    {
        "name": "Joseph",
        "location": "Pacific Heights",
        "avail_start": 8 * 60 + 15,     # 8:15 -> 495
        "avail_end": 9 * 60 + 30,       # 9:30 -> 570
        "duration": 60
    },
    {
        "name": "Steven",
        "location": "North Beach",
        "avail_start": 14 * 60 + 30,    # 14:30 -> 870
        "avail_end": 20 * 60 + 45,      # 20:45 -> 1245
        "duration": 120
    }
]

# Global variables to store the best schedule found (maximizing the number of meetings)
best_schedule = []
best_count = 0

# Backtracking function to explore meeting orders
def find_schedule(current_time, current_location, remaining_friends, current_schedule):
    global best_schedule, best_count

    # Update best schedule if current one has more meetings
    if len(current_schedule) > best_count:
        best_count = len(current_schedule)
        best_schedule = copy.deepcopy(current_schedule)
    
    # Try scheduling each friend in the remaining list
    for i, friend in enumerate(remaining_friends):
        # Determine travel time from current_location to friend's meeting location
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            continue
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start as early as when friend is available
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # If the meeting can be finished before friend's availability ends, it's feasible.
        if meeting_end <= friend["avail_end"]:
            # Create a meeting event dictionary
            event = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_str(meeting_start),
                "end_time": minutes_to_str(meeting_end)
            }
            # Prepare next state: update time and location after meeting
            next_schedule = current_schedule + [event]
            # Create a new list of remaining friends without the current one
            next_remaining = remaining_friends[:i] + remaining_friends[i+1:]
            # Recurse with updated state
            find_schedule(meeting_end, friend["location"], next_remaining, next_schedule)

# Starting parameters: arrive at Financial District at 9:00 (540 minutes)
start_time = 9 * 60  # 9:00 -> 540 minutes
start_location = "Financial District"

# Compute the optimal schedule by trying all orders.
find_schedule(start_time, start_location, friends, [])

# Prepare the output dictionary
result = {
    "itinerary": best_schedule
}

# Output the JSON result
print(json.dumps(result, indent=2))