#!/usr/bin/env python3
import json
import copy

# Convert time in minutes since midnight to a string in H:MM format.
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Travel times between locations (in minutes)
travel_times = {
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Alamo Square": 20,
        "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Russian Hill": 18,
        "Nob Hill": 16,
        "Alamo Square": 8,
        "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Embarcadero": 25,
        "Russian Hill": 21,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "The Castro": 25,
        "Golden Gate Park": 25,
        "Russian Hill": 8,
        "Nob Hill": 10,
        "Alamo Square": 19,
        "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Nob Hill": 5,
        "Alamo Square": 15,
        "North Beach": 5
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "The Castro": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Golden Gate Park": 9,
        "Embarcadero": 17,
        "Russian Hill": 13,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "North Beach": {
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Russian Hill": 4,
        "Nob Hill": 7,
        "Alamo Square": 16
    }
}

# Meeting constraints for each friend (times in minutes since midnight)
# Note: 9:00AM is 540 minutes, 7:00AM is 420, 7:30AM is 450, etc.
meetings = [
    {
        "name": "William",
        "location": "Embarcadero",
        "avail_start": 420,    # 7:00
        "avail_end": 540,      # 9:00
        "duration": 90
    },
    {
        "name": "Stephanie",
        "location": "Nob Hill",
        "avail_start": 450,    # 7:30
        "avail_end": 570,      # 9:30
        "duration": 45
    },
    {
        "name": "Joseph",
        "location": "Alamo Square",
        "avail_start": 690,    # 11:30
        "avail_end": 765,      # 12:45
        "duration": 15
    },
    {
        "name": "Karen",
        "location": "Russian Hill",
        "avail_start": 870,    # 14:30
        "avail_end": 1185,     # 19:45
        "duration": 30
    },
    {
        "name": "Kimberly",
        "location": "North Beach",
        "avail_start": 945,    # 15:45
        "avail_end": 1155,     # 19:15
        "duration": 30
    },
    {
        "name": "Laura",
        "location": "The Castro",
        "avail_start": 1185,   # 19:45
        "avail_end": 1290,     # 21:30
        "duration": 105
    },
    {
        "name": "Daniel",
        "location": "Golden Gate Park",
        "avail_start": 1275,   # 21:15
        "avail_end": 1305,     # 21:45
        "duration": 15
    }
]

# We'll use a DFS to try all feasible orders of meeting friends.
# We want to maximize the number of meetings. In case of ties we choose the one that finishes earlier.
def dfs(current_time, current_location, remaining, schedule):
    # best_result: tuple of (best_schedule, count, finish_time)
    best_schedule = copy.deepcopy(schedule)
    best_count = len(schedule)
    best_finish = current_time

    for i, friend in enumerate(remaining):
        # Get travel time from current_location to friend's location
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            continue  # skip if no route available (should not happen with given data)
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # The meeting can't start before friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if friend's availability allows the meeting
        if meeting_end > friend["avail_end"]:
            continue  # cannot fit this meeting
        # Create an event for this meeting
        event = {
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        new_schedule = copy.deepcopy(schedule)
        new_schedule.append(event)
        # Prepare remaining friends for recursive call (remove this friend)
        new_remaining = remaining[:i] + remaining[i+1:]
        # Recursively search from the new state
        rec_schedule, rec_count, rec_finish = dfs(meeting_end, friend["location"], new_remaining, new_schedule)
        # If the count from recursion is greater, update best result.
        if rec_count > best_count or (rec_count == best_count and rec_finish < best_finish):
            best_schedule = rec_schedule
            best_count = rec_count
            best_finish = rec_finish

    return best_schedule, best_count, best_finish

def main():
    # Starting state: Arrive at Fisherman's Wharf at 9:00AM (540 minutes)
    start_time = 540
    start_location = "Fisherman's Wharf"
    # Try all meetings; DFS will choose only those that are feasible.
    best_itinerary, count, finish = dfs(start_time, start_location, meetings, [])
    # Output the result as required JSON format.
    output = {"itinerary": best_itinerary}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()