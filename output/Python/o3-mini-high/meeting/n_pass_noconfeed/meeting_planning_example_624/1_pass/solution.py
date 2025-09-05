import json
import copy

# Convert HH:MM string into minutes since midnight (if needed, but here we use direct minutes for constraints)
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Travel times dictionary (in minutes)
travel_times = {
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Chinatown": 23,
        "Alamo Square": 10,
        "North Beach": 24,
        "Russian Hill": 19
    },
    "Haight-Ashbury": {
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "The Castro": 6,
        "Chinatown": 19,
        "Alamo Square": 5,
        "North Beach": 19,
        "Russian Hill": 17
    },
    "Fisherman's Wharf": {
        "Golden Gate Park": 25,
        "Haight-Ashbury": 22,
        "The Castro": 26,
        "Chinatown": 12,
        "Alamo Square": 20,
        "North Beach": 6,
        "Russian Hill": 7
    },
    "The Castro": {
        "Golden Gate Park": 11,
        "Haight-Ashbury": 6,
        "Fisherman's Wharf": 24,
        "Chinatown": 20,
        "Alamo Square": 8,
        "North Beach": 20,
        "Russian Hill": 18
    },
    "Chinatown": {
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 8,
        "The Castro": 22,
        "Alamo Square": 17,
        "North Beach": 3,
        "Russian Hill": 7
    },
    "Alamo Square": {
        "Golden Gate Park": 9,
        "Haight-Ashbury": 5,
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Chinatown": 16,
        "North Beach": 15,
        "Russian Hill": 13
    },
    "North Beach": {
        "Golden Gate Park": 22,
        "Haight-Ashbury": 18,
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Chinatown": 6,
        "Alamo Square": 16,
        "Russian Hill": 4
    },
    "Russian Hill": {
        "Golden Gate Park": 21,
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Chinatown": 9,
        "Alamo Square": 15,
        "North Beach": 5
    }
}

# Friend meeting data.
# All times are in minutes since midnight.
# 9:00 = 540. For availability, for example 21:30 = 21*60+30 = 1290.
friends_data = [
    {
        "name": "Carol",
        "location": "Haight-Ashbury",
        "avail_start": 21 * 60 + 30,  # 21:30 -> 1290
        "avail_end": 22 * 60 + 30,    # 22:30 -> 1350
        "duration": 60
    },
    {
        "name": "Laura",
        "location": "Fisherman's Wharf",
        "avail_start": 11 * 60 + 45,  # 11:45 -> 705
        "avail_end": 21 * 60 + 30,    # 21:30 -> 1290
        "duration": 60
    },
    {
        "name": "Karen",
        "location": "The Castro",
        "avail_start": 7 * 60 + 15,   # 7:15 -> 435
        "avail_end": 14 * 60,         # 14:00 -> 840
        "duration": 75
    },
    {
        "name": "Elizabeth",
        "location": "Chinatown",
        "avail_start": 12 * 60 + 15,  # 12:15 -> 735
        "avail_end": 21 * 60 + 30,    # 21:30 -> 1290
        "duration": 75
    },
    {
        "name": "Deborah",
        "location": "Alamo Square",
        "avail_start": 12 * 60,       # 12:00 -> 720
        "avail_end": 15 * 60,         # 15:00 -> 900
        "duration": 105
    },
    {
        "name": "Jason",
        "location": "North Beach",
        "avail_start": 14 * 60 + 45,  # 14:45 -> 885
        "avail_end": 19 * 60,         # 19:00 -> 1140
        "duration": 90
    },
    {
        "name": "Steven",
        "location": "Russian Hill",
        "avail_start": 14 * 60 + 45,  # 14:45 -> 885
        "avail_end": 18 * 60 + 30,    # 18:30 -> 1110
        "duration": 120
    }
]

# Recursive search to try all orders of meetings.
def search(current_location, current_time, remaining_friends, itinerary):
    best_itin = itinerary
    best_count = len(itinerary)
    
    for i, friend in enumerate(remaining_friends):
        # Get travel time from current location to friend's location.
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start when the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        
        # Check if the meeting can finish before the friend leaves.
        if meeting_end <= friend["avail_end"]:
            new_itinerary = copy.deepcopy(itinerary)
            new_itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
            candidate_itinerary, candidate_count = search(friend["location"], meeting_end, new_remaining, new_itinerary)
            if candidate_count > best_count:
                best_count = candidate_count
                best_itin = candidate_itinerary
    return best_itin, best_count

def main():
    # Starting at Golden Gate Park at 9:00
    start_location = "Golden Gate Park"
    start_time = 9 * 60  # 540 minutes
    best_schedule, count = search(start_location, start_time, friends_data, [])
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()