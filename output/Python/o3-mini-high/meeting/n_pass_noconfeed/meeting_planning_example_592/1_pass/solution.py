#!/usr/bin/env python3
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes; note that these values are directional.
travel_times = {
    "North Beach": {
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 22,
        "Nob Hill": 7
    },
    "Pacific Heights": {
        "North Beach": 9,
        "Chinatown": 11,
        "Union Square": 12,
        "Mission District": 15,
        "Golden Gate Park": 15,
        "Nob Hill": 8
    },
    "Chinatown": {
        "North Beach": 3,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 23,
        "Nob Hill": 8
    },
    "Union Square": {
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Mission District": 14,
        "Golden Gate Park": 22,
        "Nob Hill": 9
    },
    "Mission District": {
        "North Beach": 17,
        "Pacific Heights": 16,
        "Chinatown": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Nob Hill": 12
    },
    "Golden Gate Park": {
        "North Beach": 24,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Union Square": 22,
        "Mission District": 17,
        "Nob Hill": 20
    },
    "Nob Hill": {
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 13,
        "Golden Gate Park": 17
    }
}

# Define friends with their constraints.
# Times are represented in minutes from midnight.
friends = [
    {
        "name": "James",
        "location": "Pacific Heights",
        "avail_start": 20 * 60,       # 20:00 = 1200 minutes
        "avail_end": 22 * 60,         # 22:00 = 1320 minutes
        "duration": 120             # minutes to meet
    },
    {
        "name": "Robert",
        "location": "Chinatown",
        "avail_start": 12 * 60 + 15,  # 12:15 = 735 minutes
        "avail_end": 16 * 60 + 45,    # 16:45 = 1005 minutes
        "duration": 90
    },
    {
        "name": "Jeffrey",
        "location": "Union Square",
        "avail_start": 9 * 60 + 30,   # 9:30 = 570 minutes
        "avail_end": 15 * 60 + 30,    # 15:30 = 930 minutes
        "duration": 120
    },
    {
        "name": "Carol",
        "location": "Mission District",
        "avail_start": 18 * 60 + 15,  # 18:15 = 1095 minutes
        "avail_end": 21 * 60 + 15,    # 21:15 = 1275 minutes
        "duration": 15
    },
    {
        "name": "Mark",
        "location": "Golden Gate Park",
        "avail_start": 11 * 60 + 30,  # 11:30 = 690 minutes
        "avail_end": 17 * 60 + 45,    # 17:45 = 1065 minutes
        "duration": 15
    },
    {
        "name": "Sandra",
        "location": "Nob Hill",
        "avail_start": 8 * 60,        # 8:00 = 480 minutes
        "avail_end": 15 * 60 + 30,     # 15:30 = 930 minutes
        "duration": 15
    }
]

def dfs(current_loc, current_time, remaining, itinerary):
    # This DFS explores all possible meeting orders starting from current_loc and current_time.
    best_itinerary = itinerary[:]
    best_count = len(itinerary)
    
    for i, friend in enumerate(remaining):
        # Determine travel time from current location to the friend's location.
        travel_time = travel_times[current_loc][friend["location"]]
        arrival_time = current_time + travel_time
        # The meeting can start only when both you and the friend are available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # If we can finish the meeting before the friend leaves, schedule it.
        if meeting_end <= friend["avail_end"]:
            meeting_item = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_itinerary = itinerary + [meeting_item]
            # Remove the friend from the remaining list.
            new_remaining = remaining[:i] + remaining[i+1:]
            candidate_itinerary = dfs(friend["location"], meeting_end, new_remaining, new_itinerary)
            if len(candidate_itinerary) > best_count:
                best_count = len(candidate_itinerary)
                best_itinerary = candidate_itinerary
    return best_itinerary

def main():
    # Starting point: You arrive at North Beach at 9:00 AM = 540 minutes
    initial_loc = "North Beach"
    start_time = 9 * 60  # 540 minutes
    best_schedule = dfs(initial_loc, start_time, friends, [])
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()