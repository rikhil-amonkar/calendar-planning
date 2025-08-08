#!/usr/bin/env python3
import json
import itertools

# Define travel times in minutes between locations
travel_times = {
    "Richmond District": {
        "Marina District": 9,
        "Chinatown": 20,
        "Financial District": 22,
        "Bayview": 26,
        "Union Square": 21
    },
    "Marina District": {
        "Richmond District": 11,
        "Chinatown": 16,
        "Financial District": 17,
        "Bayview": 27,
        "Union Square": 16
    },
    "Chinatown": {
        "Richmond District": 20,
        "Marina District": 12,
        "Financial District": 5,
        "Bayview": 22,
        "Union Square": 7
    },
    "Financial District": {
        "Richmond District": 21,
        "Marina District": 15,
        "Chinatown": 5,
        "Bayview": 19,
        "Union Square": 9
    },
    "Bayview": {
        "Richmond District": 25,
        "Marina District": 25,
        "Chinatown": 18,
        "Financial District": 19,
        "Union Square": 17
    },
    "Union Square": {
        "Richmond District": 20,
        "Marina District": 18,
        "Chinatown": 7,
        "Financial District": 9,
        "Bayview": 15
    }
}

# Define meeting constraints for each friend.
# Times are stored as minutes after midnight.
# 9:00 AM is 540 minutes.
# For example, 9:30 AM is 570 minutes; 13:15 is 795; 16:45 is 1005; etc.
friends = [
    {
        "name": "Kimberly",
        "location": "Marina District",
        "available_start": 13 * 60 + 15,  # 13:15 -> 795
        "available_end": 16 * 60 + 45,      # 16:45 -> 1005
        "duration": 15
    },
    {
        "name": "Robert",
        "location": "Chinatown",
        "available_start": 12 * 60 + 15,    # 12:15 -> 735
        "available_end": 20 * 60 + 15,        # 20:15 -> 1215
        "duration": 15
    },
    {
        "name": "Rebecca",
        "location": "Financial District",
        "available_start": 13 * 60 + 15,    # 13:15 -> 795
        "available_end": 16 * 60 + 45,        # 16:45 -> 1005
        "duration": 75
    },
    {
        "name": "Margaret",
        "location": "Bayview",
        "available_start": 9 * 60 + 30,     # 9:30 -> 570
        "available_end": 13 * 60 + 30,        # 13:30 -> 810
        "duration": 30
    },
    {
        "name": "Kenneth",
        "location": "Union Square",
        "available_start": 19 * 60 + 30,    # 19:30 -> 1170
        "available_end": 21 * 60 + 15,        # 21:15 -> 1275
        "duration": 75
    }
]

def minutes_to_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def simulate_schedule(order):
    # Start at Richmond District at 9:00 (540 minutes)
    current_time = 540
    current_location = "Richmond District"
    itinerary = []
    
    for friend in order:
        # Travel time from current location to friend's meeting location
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        # Wait until the friend is available if arrived early
        meeting_start = max(arrival_time, friend["available_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if the meeting can be completed within the friend's available window
        if meeting_end > friend["available_end"]:
            # Cannot schedule this meeting; break out giving a partial schedule.
            break
        # Add meeting event to itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_str(meeting_start),
            "end_time": minutes_to_str(meeting_end)
        })
        # Update current time and location after meeting
        current_time = meeting_end
        current_location = friend["location"]
        
    return itinerary, current_time

def find_optimal_schedule():
    best_itinerary = None
    best_meeting_count = -1
    best_finish_time = None

    # Evaluate all permutations of friend meetings
    for order in itertools.permutations(friends):
        itinerary, finish_time = simulate_schedule(order)
        meeting_count = len(itinerary)
        # Primary objective: maximize meeting_count (i.e. number of friends met)
        # Secondary objective: finish earlier (lower finish time)
        if meeting_count > best_meeting_count or (meeting_count == best_meeting_count and (best_finish_time is None or finish_time < best_finish_time)):
            best_meeting_count = meeting_count
            best_finish_time = finish_time
            best_itinerary = itinerary
            # If we managed to schedule meetings with all friends, we can consider this optimal.
            if best_meeting_count == len(friends):
                # Continue checking in case there is an earlier finish time with full schedule.
                continue
    return best_itinerary

def main():
    optimal_itinerary = find_optimal_schedule()
    result = {"itinerary": optimal_itinerary if optimal_itinerary is not None else []}
    print(json.dumps(result))

if __name__ == "__main__":
    main()