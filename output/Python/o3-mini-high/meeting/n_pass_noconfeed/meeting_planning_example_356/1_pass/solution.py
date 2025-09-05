#!/usr/bin/env python3
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times (in minutes)
travel = {
    "Bayview": {
        "North Beach": 21,
        "Presidio": 31,
        "Haight-Ashbury": 19,
        "Union Square": 17
    },
    "North Beach": {
        "Bayview": 22,
        "Presidio": 17,
        "Haight-Ashbury": 18,
        "Union Square": 7
    },
    "Presidio": {
        "Bayview": 31,
        "North Beach": 18,
        "Haight-Ashbury": 15,
        "Union Square": 22
    },
    "Haight-Ashbury": {
        "Bayview": 18,
        "North Beach": 19,
        "Presidio": 15,
        "Union Square": 17
    },
    "Union Square": {
        "Bayview": 15,
        "North Beach": 10,
        "Presidio": 24,
        "Haight-Ashbury": 18
    }
}

# Friend meeting constraints
friends = [
    {
        "name": "Barbara",
        "location": "North Beach",
        "start": 13 * 60 + 45,  # 13:45
        "end": 20 * 60 + 15,    # 20:15
        "duration": 60
    },
    {
        "name": "Margaret",
        "location": "Presidio",
        "start": 10 * 60 + 15,  # 10:15
        "end": 15 * 60 + 15,    # 15:15
        "duration": 30
    },
    {
        "name": "Kevin",
        "location": "Haight-Ashbury",
        "start": 20 * 60 + 0,   # 20:00
        "end": 20 * 60 + 45,    # 20:45
        "duration": 30
    },
    {
        "name": "Kimberly",
        "location": "Union Square",
        "start": 7 * 60 + 45,   # 7:45
        "end": 16 * 60 + 45,    # 16:45
        "duration": 30
    }
]

def find_best_schedule(current_location, current_time, remaining_friends):
    best_schedule = []
    best_count = 0
    best_end_time = current_time

    # Base case: no more friends to schedule.
    if not remaining_friends:
        return [], 0, current_time

    for i, friend in enumerate(remaining_friends):
        # Calculate travel time from current location to friend's meeting location.
        travel_time = travel[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start when you arrive or when the friend is available.
        meeting_start = max(arrival_time, friend["start"])
        meeting_end = meeting_start + friend["duration"]

        # If meeting ends after friend's available window, skip this friend.
        if meeting_end > friend["end"]:
            continue

        meeting = {
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": to_time_str(meeting_start),
            "end_time": to_time_str(meeting_end)
        }

        # Prepare next state by removing the current friend.
        next_remaining = remaining_friends[:i] + remaining_friends[i+1:]
        next_schedule, next_count, final_time = find_best_schedule(friend["location"], meeting_end, next_remaining)
        total_count = 1 + next_count
        candidate_schedule = [meeting] + next_schedule

        # Choose the candidate with more meetings, or if equal select one with an earlier finish time.
        if total_count > best_count or (total_count == best_count and final_time < best_end_time):
            best_schedule = candidate_schedule
            best_count = total_count
            best_end_time = final_time

    return best_schedule, best_count, best_end_time

def main():
    # Start at Bayview at 9:00 AM (9*60 = 540 minutes)
    start_location = "Bayview"
    start_time = 9 * 60
    best_itinerary, count, final_time = find_best_schedule(start_location, start_time, friends)
    
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()