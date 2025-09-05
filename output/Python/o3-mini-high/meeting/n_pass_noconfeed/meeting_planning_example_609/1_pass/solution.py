import json

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def best_schedule(curr_loc, curr_time, remaining_friends, travel, friends):
    best_itinerary = []
    for friend in remaining_friends:
        info = friends[friend]
        # Calculate arrival time at friend's location
        travel_time = travel[curr_loc][info["location"]]
        arrival_time = curr_time + travel_time
        # The meeting can only start once you have arrived and the friend is available.
        meeting_start = max(arrival_time, info["avail_start"])
        meeting_end = meeting_start + info["duration"]
        # Check if meeting can finish before the friend’s availability ends.
        if meeting_end <= info["avail_end"]:
            step = {
                "action": "meet",
                "location": info["location"],
                "person": friend,
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            }
            new_remaining = remaining_friends.copy()
            new_remaining.remove(friend)
            subsequent = best_schedule(info["location"], meeting_end, new_remaining, travel, friends)
            itinerary_candidate = [step] + subsequent
            if len(itinerary_candidate) > len(best_itinerary):
                best_itinerary = itinerary_candidate
    return best_itinerary

def main():
    # Travel times (in minutes) between locations
    travel = {
        "Chinatown": {
            "Mission District": 18,
            "Alamo Square": 17,
            "Pacific Heights": 10,
            "Union Square": 7,
            "Golden Gate Park": 23,
            "Sunset District": 29,
            "Presidio": 19,
        },
        "Mission District": {
            "Chinatown": 16,
            "Alamo Square": 11,
            "Pacific Heights": 16,
            "Union Square": 15,
            "Golden Gate Park": 17,
            "Sunset District": 24,
            "Presidio": 25,
        },
        "Alamo Square": {
            "Chinatown": 16,
            "Mission District": 10,
            "Pacific Heights": 10,
            "Union Square": 14,
            "Golden Gate Park": 9,
            "Sunset District": 16,
            "Presidio": 18,
        },
        "Pacific Heights": {
            "Chinatown": 11,
            "Mission District": 15,
            "Alamo Square": 10,
            "Union Square": 12,
            "Golden Gate Park": 15,
            "Sunset District": 21,
            "Presidio": 11,
        },
        "Union Square": {
            "Chinatown": 7,
            "Mission District": 14,
            "Alamo Square": 15,
            "Pacific Heights": 15,
            "Golden Gate Park": 22,
            "Sunset District": 26,
            "Presidio": 24,
        },
        "Golden Gate Park": {
            "Chinatown": 23,
            "Mission District": 17,
            "Alamo Square": 10,
            "Pacific Heights": 16,
            "Union Square": 22,
            "Sunset District": 10,
            "Presidio": 11,
        },
        "Sunset District": {
            "Chinatown": 30,
            "Mission District": 24,
            "Alamo Square": 17,
            "Pacific Heights": 21,
            "Union Square": 30,
            "Golden Gate Park": 11,
            "Presidio": 16,
        },
        "Presidio": {
            "Chinatown": 21,
            "Mission District": 26,
            "Alamo Square": 18,
            "Pacific Heights": 11,
            "Union Square": 22,
            "Golden Gate Park": 12,
            "Sunset District": 15,
        }
    }
    
    # Friend meeting constraints.
    # Times are represented as minutes since midnight for ease of calculation.
    # For example, 9:00 AM is 9*60 = 540.
    friends = {
        "David": {
            "location": "Mission District",
            "avail_start": 8 * 60,          # 8:00 AM => 480 minutes
            "avail_end": 19 * 60 + 45,       # 7:45 PM => 1185 minutes
            "duration": 45
        },
        "Kenneth": {
            "location": "Alamo Square",
            "avail_start": 14 * 60,          # 2:00 PM => 840 minutes
            "avail_end": 19 * 60 + 45,       # 7:45 PM => 1185 minutes
            "duration": 120
        },
        "John": {
            "location": "Pacific Heights",
            "avail_start": 17 * 60,          # 5:00 PM => 1020 minutes
            "avail_end": 20 * 60,            # 8:00 PM => 1200 minutes
            "duration": 15
        },
        "Charles": {
            "location": "Union Square",
            "avail_start": 21 * 60 + 45,     # 9:45 PM => 1305 minutes
            "avail_end": 22 * 60 + 45,       # 10:45 PM => 1365 minutes
            "duration": 60
        },
        "Deborah": {
            "location": "Golden Gate Park",
            "avail_start": 7 * 60,           # 7:00 AM => 420 minutes
            "avail_end": 18 * 60 + 15,       # 6:15 PM => 1095 minutes
            "duration": 90
        },
        "Karen": {
            "location": "Sunset District",
            "avail_start": 17 * 60 + 45,     # 5:45 PM => 1065 minutes
            "avail_end": 21 * 60 + 15,       # 9:15 PM => 1275 minutes
            "duration": 15
        },
        "Carol": {
            "location": "Presidio",
            "avail_start": 8 * 60 + 15,      # 8:15 AM => 495 minutes
            "avail_end": 9 * 60 + 15,        # 9:15 AM => 555 minutes
            "duration": 30
        }
    }
    
    # You arrive at Chinatown at 9:00 AM (540 minutes).
    start_location = "Chinatown"
    start_time = 9 * 60  # 9:00 AM
    
    available_friends = list(friends.keys())
    
    # Compute the optimal meeting schedule (maximizing the number of friends met)
    itinerary = best_schedule(start_location, start_time, available_friends, travel, friends)
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()