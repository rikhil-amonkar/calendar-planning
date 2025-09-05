import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times between locations (in minutes)
travel_times = {
    "Pacific Heights": {
        "Nob Hill": 8,
        "Russian Hill": 7,
        "The Castro": 16,
        "Sunset District": 21,
        "Haight-Ashbury": 11
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Russian Hill": 5,
        "The Castro": 17,
        "Sunset District": 25,
        "Haight-Ashbury": 13
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Nob Hill": 5,
        "The Castro": 21,
        "Sunset District": 23,
        "Haight-Ashbury": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Russian Hill": 18,
        "Sunset District": 17,
        "Haight-Ashbury": 6
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Nob Hill": 27,
        "Russian Hill": 24,
        "The Castro": 17,
        "Haight-Ashbury": 15
    },
    "Haight-Ashbury": {
        "Pacific Heights": 12,
        "Nob Hill": 15,
        "Russian Hill": 17,
        "The Castro": 6,
        "Sunset District": 15
    }
}

# Meeting constraints for each friend.
# Times are represented in minutes from midnight.
# 9:00AM is 540, 10:00AM is 600, etc.
friends = {
    "Ronald": {
        "location": "Nob Hill",
        "avail_start": 600,   # 10:00
        "avail_end": 1020,    # 17:00
        "duration": 105       # minutes required
    },
    "Sarah": {
        "location": "Russian Hill",
        "avail_start": 435,   # 7:15
        "avail_end": 570,     # 9:30
        "duration": 45
    },
    "Helen": {
        "location": "The Castro",
        "avail_start": 810,   # 13:30
        "avail_end": 1020,    # 17:00
        "duration": 120
    },
    "Joshua": {
        "location": "Sunset District",
        "avail_start": 855,   # 14:15
        "avail_end": 1170,    # 19:30
        "duration": 90
    },
    "Margaret": {
        "location": "Haight-Ashbury",
        "avail_start": 615,   # 10:15
        "avail_end": 1320,    # 22:00
        "duration": 60
    }
}

def backtrack(current_time, current_location, remaining, current_schedule):
    best_schedule = current_schedule[:]
    for friend in remaining:
        friend_info = friends[friend]
        # Get travel time from the current location to the friend's location
        if current_location in travel_times and friend_info["location"] in travel_times[current_location]:
            travel = travel_times[current_location][friend_info["location"]]
        else:
            continue
        
        arrival_time = current_time + travel
        meeting_start = max(arrival_time, friend_info["avail_start"])
        meeting_end = meeting_start + friend_info["duration"]
        
        # Check if we can complete the meeting within the friend's available time
        if meeting_end <= friend_info["avail_end"]:
            event = {
                "person": friend,
                "location": friend_info["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            new_schedule = current_schedule[:] + [event]
            new_remaining = remaining[:]
            new_remaining.remove(friend)
            candidate_schedule = backtrack(meeting_end, friend_info["location"], new_remaining, new_schedule)
            if len(candidate_schedule) > len(best_schedule):
                best_schedule = candidate_schedule
    return best_schedule

def main():
    # You arrive at Pacific Heights at 9:00AM (540 minutes from midnight)
    start_time = 540
    start_location = "Pacific Heights"
    
    # List of all friends’ names
    all_friends = list(friends.keys())
    
    # Compute the optimal meeting schedule using backtracking
    optimal_schedule = backtrack(start_time, start_location, all_friends, [])
    
    # Format the itinerary for JSON output with times in "H:MM" 24-hour format
    itinerary = []
    for event in optimal_schedule:
        itinerary.append({
            "action": "meet",
            "location": event["location"],
            "person": event["person"],
            "start_time": minutes_to_time(event["start"]),
            "end_time": minutes_to_time(event["end"])
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()