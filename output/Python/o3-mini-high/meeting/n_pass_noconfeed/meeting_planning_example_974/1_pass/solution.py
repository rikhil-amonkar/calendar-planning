#!/usr/bin/env python3
import json

def minutes_to_time(m):
    """Convert minutes from midnight to a H:MM string (24‑hour format)."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Hard‑coded travel times (in minutes) between locations.
travel_times = {
    "Sunset District": {
        "Presidio": 16,
        "Nob Hill": 27,
        "Pacific Heights": 21,
        "Mission District": 25,
        "Marina District": 21,
        "North Beach": 28,
        "Russian Hill": 24,
        "Richmond District": 12,
        "Embarcadero": 30,
        "Alamo Square": 17
    },
    "Presidio": {
        "Sunset District": 15,
        "Nob Hill": 18,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Marina District": 11,
        "North Beach": 18,
        "Russian Hill": 14,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Alamo Square": 19
    },
    "Nob Hill": {
        "Sunset District": 24,
        "Presidio": 17,
        "Pacific Heights": 8,
        "Mission District": 13,
        "Marina District": 11,
        "North Beach": 8,
        "Russian Hill": 5,
        "Richmond District": 14,
        "Embarcadero": 9,
        "Alamo Square": 11
    },
    "Pacific Heights": {
        "Sunset District": 21,
        "Presidio": 11,
        "Nob Hill": 8,
        "Mission District": 15,
        "Marina District": 6,
        "North Beach": 9,
        "Russian Hill": 7,
        "Richmond District": 12,
        "Embarcadero": 10,
        "Alamo Square": 10
    },
    "Mission District": {
        "Sunset District": 24,
        "Presidio": 25,
        "Nob Hill": 12,
        "Pacific Heights": 16,
        "Marina District": 19,
        "North Beach": 17,
        "Russian Hill": 15,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Alamo Square": 11
    },
    "Marina District": {
        "Sunset District": 19,
        "Presidio": 10,
        "Nob Hill": 12,
        "Pacific Heights": 7,
        "Mission District": 20,
        "North Beach": 11,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Alamo Square": 15
    },
    "North Beach": {
        "Sunset District": 27,
        "Presidio": 17,
        "Nob Hill": 7,
        "Pacific Heights": 8,
        "Mission District": 18,
        "Marina District": 9,
        "Russian Hill": 4,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Alamo Square": 16
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Presidio": 14,
        "Nob Hill": 5,
        "Pacific Heights": 7,
        "Mission District": 16,
        "Marina District": 7,
        "North Beach": 5,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Alamo Square": 15
    },
    "Richmond District": {
        "Sunset District": 11,
        "Presidio": 7,
        "Nob Hill": 17,
        "Pacific Heights": 10,
        "Mission District": 20,
        "Marina District": 9,
        "North Beach": 17,
        "Russian Hill": 13,
        "Embarcadero": 19,
        "Alamo Square": 13
    },
    "Embarcadero": {
        "Sunset District": 30,
        "Presidio": 20,
        "Nob Hill": 10,
        "Pacific Heights": 11,
        "Mission District": 20,
        "Marina District": 12,
        "North Beach": 5,
        "Russian Hill": 8,
        "Richmond District": 21,
        "Alamo Square": 19
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Presidio": 17,
        "Nob Hill": 11,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Marina District": 15,
        "North Beach": 15,
        "Russian Hill": 13,
        "Richmond District": 11,
        "Embarcadero": 16
    }
}

# Friends' meeting constraints.
# Times are represented in minutes from midnight.
friends = {
    "Charles": {
        "location": "Presidio",
        "avail_start": 13 * 60 + 15,  # 13:15 = 795
        "avail_end": 15 * 60,         # 15:00 = 900
        "duration": 105
    },
    "Robert": {
        "location": "Nob Hill",
        "avail_start": 13 * 60 + 15,  # 13:15 = 795
        "avail_end": 17 * 60 + 30,    # 17:30 = 1050
        "duration": 90
    },
    "Nancy": {
        "location": "Pacific Heights",
        "avail_start": 14 * 60 + 45,  # 14:45 = 885
        "avail_end": 22 * 60,         # 22:00 = 1320
        "duration": 105
    },
    "Brian": {
        "location": "Mission District",
        "avail_start": 15 * 60 + 30,  # 15:30 = 930
        "avail_end": 22 * 60,         # 22:00 = 1320
        "duration": 60
    },
    "Kimberly": {
        "location": "Marina District",
        "avail_start": 17 * 60,       # 17:00 = 1020
        "avail_end": 19 * 60 + 45,    # 19:45 = 1185
        "duration": 75
    },
    "David": {
        "location": "North Beach",
        "avail_start": 14 * 60 + 45,  # 14:45 = 885
        "avail_end": 16 * 60 + 30,    # 16:30 = 990
        "duration": 75
    },
    "William": {
        "location": "Russian Hill",
        "avail_start": 12 * 60 + 30,  # 12:30 = 750
        "avail_end": 19 * 60 + 15,    # 19:15 = 1155
        "duration": 120
    },
    "Jeffrey": {
        "location": "Richmond District",
        "avail_start": 12 * 60,       # 12:00 = 720
        "avail_end": 19 * 60 + 15,    # 19:15 = 1155
        "duration": 45
    },
    "Karen": {
        "location": "Embarcadero",
        "avail_start": 14 * 60 + 15,  # 14:15 = 855
        "avail_end": 20 * 60 + 45,    # 20:45 = 1245
        "duration": 60
    },
    "Joshua": {
        "location": "Alamo Square",
        "avail_start": 18 * 60 + 45,  # 18:45 = 1125
        "avail_end": 22 * 60,         # 22:00 = 1320
        "duration": 60
    }
}

def search_itinerary(current_time, current_loc, remaining, itinerary):
    """
    Recursively search for a meeting itinerary that maximizes the number of meetings.
    For each friend not yet met, check if travel + waiting allows scheduling the meeting
    within the friend’s available window. If so, schedule it and continue the search.
    """
    best_itinerary = list(itinerary)  # copy current itinerary as the best so far
    for friend in remaining:
        info = friends[friend]
        # Calculate when we arrive at the friend’s location.
        travel_time = travel_times[current_loc][info["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, info["avail_start"])
        meeting_end = meeting_start + info["duration"]
        # Check if the meeting can be completed within the friend's available window.
        if meeting_end <= info["avail_end"]:
            event = {
                "action": "meet",
                "location": info["location"],
                "person": friend,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_remaining = [f for f in remaining if f != friend]
            new_itinerary = itinerary + [event]
            candidate_itinerary = search_itinerary(meeting_end, info["location"], new_remaining, new_itinerary)
            if len(candidate_itinerary) > len(best_itinerary):
                best_itinerary = candidate_itinerary
    return best_itinerary

if __name__ == "__main__":
    # Start at Sunset District at 9:00 (9*60 = 540 minutes).
    start_time = 9 * 60
    start_location = "Sunset District"
    all_friends = list(friends.keys())
    
    # Compute the optimal itinerary.
    optimal_itinerary = search_itinerary(start_time, start_location, all_friends, [])
    
    # Build the result in the specified JSON format.
    result = {
        "itinerary": optimal_itinerary
    }
    print(json.dumps(result, indent=2))