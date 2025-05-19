#!/usr/bin/env python3
import itertools
import json
import math

def minutes_to_time_str(t):
    # t is minutes since midnight
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Define travel times in minutes as a nested dictionary.
travel_times = {
    "Chinatown": {
        "Embarcadero": 5,
        "Pacific Heights": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Fisherman's Wharf": 8,
        "Sunset District": 29,
        "The Castro": 22
    },
    "Embarcadero": {
        "Chinatown": 7,
        "Pacific Heights": 11,
        "Russian Hill": 8,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Fisherman's Wharf": 6,
        "Sunset District": 30,
        "The Castro": 25
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Embarcadero": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Sunset District": 21,
        "The Castro": 16
    },
    "Russian Hill": {
        "Chinatown": 9,
        "Embarcadero": 8,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Golden Gate Park": 21,
        "Fisherman's Wharf": 7,
        "Sunset District": 23,
        "The Castro": 21
    },
    "Haight-Ashbury": {
        "Chinatown": 19,
        "Embarcadero": 20,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "Sunset District": 15,
        "The Castro": 6
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Embarcadero": 25,
        "Pacific Heights": 16,
        "Russian Hill": 19,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Sunset District": 10,
        "The Castro": 13
    },
    "Fisherman's Wharf": {
        "Chinatown": 12,
        "Embarcadero": 8,
        "Pacific Heights": 12,
        "Russian Hill": 7,
        "Haight-Ashbury": 22,
        "Golden Gate Park": 25,
        "Sunset District": 27,
        "The Castro": 27
    },
    "Sunset District": {
        "Chinatown": 30,
        "Embarcadero": 30,
        "Pacific Heights": 21,
        "Russian Hill": 24,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "The Castro": 17
    },
    "The Castro": {
        "Chinatown": 22,
        "Embarcadero": 22,
        "Pacific Heights": 16,
        "Russian Hill": 18,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 24,
        "Sunset District": 17
    }
}

# Define the meeting constraints.
# Times are represented as minutes after midnight.
appointments = [
    {
        "person": "Richard",
        "location": "Embarcadero",
        "avail_start": 15 * 60 + 15,   # 15:15 -> 915
        "avail_end": 18 * 60 + 45,      # 18:45 -> 1125
        "duration": 90
    },
    {
        "person": "Mark",
        "location": "Pacific Heights",
        "avail_start": 15 * 60 + 0,     # 15:00 -> 900
        "avail_end": 17 * 60 + 0,       # 17:00 -> 1020
        "duration": 45
    },
    {
        "person": "Matthew",
        "location": "Russian Hill",
        "avail_start": 17 * 60 + 30,    # 17:30 -> 1050
        "avail_end": 21 * 60 + 0,       # 21:00 -> 1260
        "duration": 90
    },
    {
        "person": "Rebecca",
        "location": "Haight-Ashbury",
        "avail_start": 14 * 60 + 45,    # 14:45 -> 885
        "avail_end": 18 * 60 + 0,       # 18:00 -> 1080
        "duration": 60
    },
    {
        "person": "Melissa",
        "location": "Golden Gate Park",
        "avail_start": 13 * 60 + 45,    # 13:45 -> 825
        "avail_end": 17 * 60 + 30,      # 17:30 -> 1050
        "duration": 90
    },
    {
        "person": "Margaret",
        "location": "Fisherman's Wharf",
        "avail_start": 14 * 60 + 45,    # 14:45 -> 885
        "avail_end": 20 * 60 + 15,      # 20:15 -> 1215
        "duration": 15
    },
    {
        "person": "Emily",
        "location": "Sunset District",
        "avail_start": 15 * 60 + 45,    # 15:45 -> 945
        "avail_end": 17 * 60 + 0,       # 17:00 -> 1020
        "duration": 45
    },
    {
        "person": "George",
        "location": "The Castro",
        "avail_start": 14 * 60 + 0,     # 14:00 -> 840
        "avail_end": 16 * 60 + 15,      # 16:15 -> 975
        "duration": 75
    }
]

# Starting location and time
START_LOCATION = "Chinatown"
START_TIME = 9 * 60  # 9:00 = 540 minutes

def compute_schedule_for_order(order):
    schedule = []
    current_time = START_TIME
    current_loc = START_LOCATION
    for app in order:
        # get travel time from current_loc to appointment's location
        if current_loc not in travel_times or app["location"] not in travel_times[current_loc]:
            return None  # travel time undefined, not feasible
        travel_time = travel_times[current_loc][app["location"]]
        current_time += travel_time
        # Meeting cannot start before the available start time.
        meeting_start = max(current_time, app["avail_start"])
        meeting_end = meeting_start + app["duration"]
        # Check if meeting ends within available window.
        if meeting_end > app["avail_end"]:
            return None  # not feasible
        # Record the meeting schedule.
        schedule.append({
            "action": "meet",
            "location": app["location"],
            "person": app["person"],
            "start_time": meeting_start,
            "end_time": meeting_end
        })
        # update current time and location
        current_time = meeting_end
        current_loc = app["location"]
    return schedule, current_time

def convert_schedule_times(schedule):
    converted = []
    for event in schedule:
        converted.append({
            "action": event["action"],
            "location": event["location"],
            "person": event["person"],
            "start_time": minutes_to_time_str(event["start_time"]),
            "end_time": minutes_to_time_str(event["end_time"])
        })
    return converted

def main():
    best_schedule = None
    best_count = 0
    best_finish = math.inf

    n = len(appointments)
    # We will try all possible orders (of any subset size) to maximize number of meetings.
    # For each size from 1 to n, consider all permutations.
    for r in range(1, n+1):
        for order in itertools.permutations(appointments, r):
            result = compute_schedule_for_order(order)
            if result is not None:
                schedule, finish_time = result
                count = len(schedule)
                # Update if more meetings are scheduled or same count but earlier finish.
                if count > best_count or (count == best_count and finish_time < best_finish):
                    best_schedule = schedule
                    best_count = count
                    best_finish = finish_time

    # If we found a schedule, convert times to required string format.
    if best_schedule is not None:
        best_schedule_converted = convert_schedule_times(best_schedule)
    else:
        best_schedule_converted = []

    itinerary = {"itinerary": best_schedule_converted}
    print(json.dumps(itinerary, indent=2))

if __name__ == '__main__':
    main()