#!/usr/bin/env python3
import json
from itertools import permutations

# Helper functions to convert time formats
def time_to_minutes(time_str):
    # time_str format "H:MM"
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    # Convert minutes since midnight to "H:MM" (24hr format, no leading zero for hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Input constraints as variables
# Starting point and time (Bayview at 9:00AM)
start_location = "Bayview"
start_time = time_to_minutes("9:00")

# Meeting constraints: each friend has location, availability window and minimum meeting duration (in minutes)
meetings = [
    {
        "person": "Joseph",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("8:30"),
        "avail_end": time_to_minutes("19:15"),
        "min_duration": 60
    },
    {
        "person": "Nancy",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("11:00"),
        "avail_end": time_to_minutes("16:00"),
        "min_duration": 90
    },
    {
        "person": "Jason",
        "location": "North Beach",
        "avail_start": time_to_minutes("16:45"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 15
    },
    {
        "person": "Jeffrey",
        "location": "Financial District",
        "avail_start": time_to_minutes("10:30"),
        "avail_end": time_to_minutes("15:45"),
        "min_duration": 45
    }
]

# Travel times in minutes between locations
# travel_times[from_location][to_location] = minutes
travel_times = {
    "Bayview": {
        "Russian Hill": 23,
        "Alamo Square": 16,
        "North Beach": 21,
        "Financial District": 19
    },
    "Russian Hill": {
        "Bayview": 23,
        "Alamo Square": 15,
        "North Beach": 5,
        "Financial District": 11
    },
    "Alamo Square": {
        "Bayview": 16,
        "Russian Hill": 13,
        "North Beach": 15,
        "Financial District": 17
    },
    "North Beach": {
        "Bayview": 22,
        "Russian Hill": 4,
        "Alamo Square": 16,
        "Financial District": 8
    },
    "Financial District": {
        "Bayview": 19,
        "Russian Hill": 10,
        "Alamo Square": 17,
        "North Beach": 7
    }
}

def compute_schedule(order):
    """
    Given an ordering (permutation) of meetings, try to build a schedule.
    Returns (is_valid, itinerary, finish_time)
    itinerary is a list of scheduled meetings with computed start and end times.
    finish_time is the finishing time (in minutes) after last meeting.
    """
    itinerary = []
    current_time = start_time
    current_location = start_location

    for meeting in order:
        meeting_location = meeting["location"]
        # Determine travel time from current location to meeting location
        if current_location == meeting_location:
            travel_time = 0
        else:
            travel_time = travel_times[current_location][meeting_location]
        arrival_time = current_time + travel_time

        # Meeting can only start when person is available.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]

        # Check if meeting can finish before the person's availability ends.
        if meeting_end > meeting["avail_end"]:
            return (False, None, None)

        # Record this meeting in itinerary (with time formatted)
        itinerary.append({
            "action": "meet",
            "location": meeting_location,
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })

        # Update current time and location
        current_time = meeting_end
        current_location = meeting_location

    return (True, itinerary, current_time)

def main():
    best_itinerary = None
    best_finish_time = None
    best_meetings_count = 0

    # Try all permutations of meeting orders.
    for order in permutations(meetings):
        valid, itinerary, finish_time = compute_schedule(order)
        if valid:
            # Count number of meetings scheduled.
            count = len(itinerary)
            # We want to maximize number of meetings and then minimize finish time.
            if count > best_meetings_count or (count == best_meetings_count and (best_finish_time is None or finish_time < best_finish_time)):
                best_meetings_count = count
                best_finish_time = finish_time
                best_itinerary = itinerary

    # Prepare the output dictionary
    output = {
        "itinerary": best_itinerary if best_itinerary is not None else []
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()