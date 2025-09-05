import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Friend meeting constraints in minutes since midnight.
# Times are represented in minutes for ease of calculation.
friends = {
    "Matthew": {
        "location": "The Castro",
        "available_start": 16 * 60 + 30,  # 16:30 -> 990
        "available_end": 20 * 60,         # 20:00 -> 1200
        "min_meeting": 45
    },
    "Rebecca": {
        "location": "Nob Hill",
        "available_start": 15 * 60 + 15,  # 15:15 -> 915
        "available_end": 19 * 60 + 15,      # 19:15 -> 1155
        "min_meeting": 105
    },
    "Brian": {
        "location": "Marina District",
        "available_start": 14 * 60 + 15,  # 14:15 -> 855
        "available_end": 22 * 60,         # 22:00 -> 1320
        "min_meeting": 30
    },
    "Emily": {
        "location": "Pacific Heights",
        "available_start": 11 * 60 + 15,  # 11:15 -> 675
        "available_end": 19 * 60 + 45,      # 19:45 -> 1185
        "min_meeting": 15
    },
    "Karen": {
        "location": "Haight-Ashbury",
        "available_start": 11 * 60 + 45,  # 11:45 -> 705
        "available_end": 17 * 60 + 30,      # 17:30 -> 1050
        "min_meeting": 30
    },
    "Stephanie": {
        "location": "Mission District",
        "available_start": 13 * 60,       # 13:00 -> 780
        "available_end": 15 * 60 + 45,      # 15:45 -> 945
        "min_meeting": 75
    },
    "James": {
        "location": "Chinatown",
        "available_start": 14 * 60 + 30,  # 14:30 -> 870
        "available_end": 19 * 60,         # 19:00 -> 1140
        "min_meeting": 120
    },
    "Steven": {
        "location": "Russian Hill",
        "available_start": 14 * 60,       # 14:00 -> 840
        "available_end": 20 * 60,         # 20:00 -> 1200
        "min_meeting": 30
    },
    "Elizabeth": {
        "location": "Alamo Square",
        "available_start": 13 * 60,       # 13:00 -> 780
        "available_end": 17 * 60 + 15,      # 17:15 -> 1035
        "min_meeting": 120
    },
    "William": {
        "location": "Bayview",
        "available_start": 18 * 60 + 15,  # 18:15 -> 1095
        "available_end": 20 * 60 + 15,      # 20:15 -> 1215
        "min_meeting": 90
    }
}

# Travel times (in minutes) between locations.
travel_times = {
    "Richmond District": {
        "The Castro": 16,
        "Nob Hill": 17,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Chinatown": 20,
        "Russian Hill": 13,
        "Alamo Square": 13,
        "Bayview": 27,
    },
    "The Castro": {
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Chinatown": 22,
        "Russian Hill": 18,
        "Alamo Square": 8,
        "Bayview": 19,
    },
    "Nob Hill": {
        "Richmond District": 14,
        "The Castro": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Mission District": 13,
        "Chinatown": 6,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "Bayview": 19,
    },
    "Marina District": {
        "Richmond District": 11,
        "The Castro": 22,
        "Nob Hill": 12,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Chinatown": 15,
        "Russian Hill": 8,
        "Alamo Square": 15,
        "Bayview": 27,
    },
    "Pacific Heights": {
        "Richmond District": 12,
        "The Castro": 16,
        "Nob Hill": 8,
        "Marina District": 6,
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Chinatown": 11,
        "Russian Hill": 7,
        "Alamo Square": 10,
        "Bayview": 22,
    },
    "Haight-Ashbury": {
        "Richmond District": 10,
        "The Castro": 6,
        "Nob Hill": 15,
        "Marina District": 17,
        "Pacific Heights": 12,
        "Mission District": 11,
        "Chinatown": 19,
        "Russian Hill": 17,
        "Alamo Square": 5,
        "Bayview": 18,
    },
    "Mission District": {
        "Richmond District": 20,
        "The Castro": 7,
        "Nob Hill": 12,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Haight-Ashbury": 12,
        "Chinatown": 16,
        "Russian Hill": 15,
        "Alamo Square": 11,
        "Bayview": 14,
    },
    "Chinatown": {
        "Richmond District": 20,
        "The Castro": 22,
        "Nob Hill": 9,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Haight-Ashbury": 19,
        "Mission District": 17,
        "Russian Hill": 7,
        "Alamo Square": 17,
        "Bayview": 20,
    },
    "Russian Hill": {
        "Richmond District": 14,
        "The Castro": 21,
        "Nob Hill": 5,
        "Marina District": 7,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Chinatown": 9,
        "Alamo Square": 15,
        "Bayview": 23,
    },
    "Alamo Square": {
        "Richmond District": 11,
        "The Castro": 8,
        "Nob Hill": 11,
        "Marina District": 15,
        "Pacific Heights": 10,
        "Haight-Ashbury": 5,
        "Mission District": 10,
        "Chinatown": 15,
        "Russian Hill": 13,
        "Bayview": 16,
    },
    "Bayview": {
        "Richmond District": 25,
        "The Castro": 19,
        "Nob Hill": 20,
        "Marina District": 27,
        "Pacific Heights": 23,
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Chinatown": 19,
        "Russian Hill": 23,
        "Alamo Square": 16,
    }
}

def search(current_time, current_location, remaining_friends, current_schedule):
    best_schedule = current_schedule[:]
    # Try to schedule meetings with each remaining friend
    for friend in remaining_friends:
        friend_data = friends[friend]
        # Determine travel time from current location to friend's location
        travel = travel_times[current_location][friend_data["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when the friend is available.
        meeting_start = max(arrival_time, friend_data["available_start"])
        meeting_end = meeting_start + friend_data["min_meeting"]
        # Check if the meeting can be completed before the friend's availability ends.
        if meeting_end > friend_data["available_end"]:
            continue  # Not enough time for the meeting, skip this friend.
        
        # Create a meeting event for this friend.
        event = {
            "action": "meet",
            "location": friend_data["location"],
            "person": friend,
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        }
        
        new_schedule = current_schedule + [event]
        new_remaining = remaining_friends[:]
        new_remaining.remove(friend)
        
        candidate_schedule = search(meeting_end, friend_data["location"], new_remaining, new_schedule)
        if len(candidate_schedule) > len(best_schedule):
            best_schedule = candidate_schedule
    return best_schedule

def main():
    # Arrival at Richmond District at 9:00AM
    start_time = 9 * 60  # 9:00 in minutes
    start_location = "Richmond District"
    all_friends = list(friends.keys())
    
    optimal_schedule = search(start_time, start_location, all_friends, [])
    
    result = {"itinerary": optimal_schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()