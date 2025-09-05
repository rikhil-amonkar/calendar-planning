#!/usr/bin/env python3
import itertools
import json

def minutes_to_time_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times in minutes between locations
    travel_times = {
        "Presidio": {
            "Golden Gate Park": 12,
            "Bayview": 31,
            "Chinatown": 21,
            "North Beach": 18,
            "Mission District": 26,
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Bayview": 23,
            "Chinatown": 23,
            "North Beach": 24,
            "Mission District": 17,
        },
        "Bayview": {
            "Presidio": 31,
            "Golden Gate Park": 22,
            "Chinatown": 18,
            "North Beach": 21,
            "Mission District": 13,
        },
        "Chinatown": {
            "Presidio": 19,
            "Golden Gate Park": 23,
            "Bayview": 22,
            "North Beach": 3,
            "Mission District": 18,
        },
        "North Beach": {
            "Presidio": 17,
            "Golden Gate Park": 22,
            "Bayview": 22,
            "Chinatown": 6,
            "Mission District": 18,
        },
        "Mission District": {
            "Presidio": 25,
            "Golden Gate Park": 17,
            "Bayview": 15,
            "Chinatown": 16,
            "North Beach": 17,
        },
    }

    # Define friends' meeting constraints.
    # Times are represented in minutes from midnight.
    friends = {
        "Jessica": {
            "location": "Golden Gate Park",
            "avail_start": 13 * 60 + 45,  # 13:45 -> 825 minutes
            "avail_end": 15 * 60,         # 15:00 -> 900 minutes
            "duration": 30
        },
        "Ashley": {
            "location": "Bayview",
            "avail_start": 17 * 60 + 15,  # 17:15 -> 1035 minutes
            "avail_end": 20 * 60,         # 20:00 -> 1200 minutes
            "duration": 105
        },
        "Ronald": {
            "location": "Chinatown",
            "avail_start": 7 * 60 + 15,   # 7:15 -> 435 minutes
            "avail_end": 14 * 60 + 45,    # 14:45 -> 885 minutes
            "duration": 90
        },
        "William": {
            "location": "North Beach",
            "avail_start": 13 * 60 + 15,  # 13:15 -> 795 minutes
            "avail_end": 20 * 60 + 15,    # 20:15 -> 1215 minutes
            "duration": 15
        },
        "Daniel": {
            "location": "Mission District",
            "avail_start": 7 * 60,        # 7:00 -> 420 minutes
            "avail_end": 11 * 60 + 15,      # 11:15 -> 675 minutes
            "duration": 105
        },
    }

    # Starting parameters
    start_time = 9 * 60  # 9:00 AM -> 540 minutes
    start_location = "Presidio"
    friend_names = list(friends.keys())

    best_schedule = None
    best_finish_time = float('inf')
    max_meetings = 0

    # Try all permutations of friend meetings and compute a feasible schedule
    for perm in itertools.permutations(friend_names):
        schedule = []
        current_time = start_time
        current_location = start_location
        valid = True

        for friend in perm:
            data = friends[friend]
            # Compute travel time from current location to the friend's location.
            travel = travel_times[current_location][data["location"]]
            arrival_time = current_time + travel
            # Meeting can only start when both you have arrived and the friend is available.
            meeting_start = max(arrival_time, data["avail_start"])
            meeting_end = meeting_start + data["duration"]
            # If the meeting ends after the friend's availability window, this order is invalid.
            if meeting_end > data["avail_end"]:
                valid = False
                break
            # Append the meeting to the schedule
            schedule.append({
                "action": "meet",
                "location": data["location"],
                "person": friend,
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            })
            # Update current time and location for the next meeting.
            current_time = meeting_end
            current_location = data["location"]

        # Select the schedule with the maximum number of meetings.
        # If equal, choose the one that finishes earlier.
        if valid:
            if len(schedule) > max_meetings:
                max_meetings = len(schedule)
                best_schedule = schedule
                best_finish_time = current_time
            elif len(schedule) == max_meetings and current_time < best_finish_time:
                best_schedule = schedule
                best_finish_time = current_time

    result = {"itinerary": best_schedule if best_schedule is not None else []}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()