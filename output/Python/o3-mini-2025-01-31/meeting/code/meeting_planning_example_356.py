#!/usr/bin/env python3
import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    # time_str format: H:MM (24-hour)
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes as given
travel_times = {
    "Bayview": {"North Beach": 21, "Presidio": 31, "Haight-Ashbury": 19, "Union Square": 17},
    "North Beach": {"Bayview": 22, "Presidio": 17, "Haight-Ashbury": 18, "Union Square": 7},
    "Presidio": {"Bayview": 31, "North Beach": 18, "Haight-Ashbury": 15, "Union Square": 22},
    "Haight-Ashbury": {"Bayview": 18, "North Beach": 19, "Presidio": 15, "Union Square": 17},
    "Union Square": {"Bayview": 15, "North Beach": 10, "Presidio": 24, "Haight-Ashbury": 18}
}

# Meeting constraints for each friend
# Each friend is defined by: location, available start time, available end time, meeting duration (in minutes)
friends = {
    "Barbara": {
        "location": "North Beach",
        "avail_start": time_to_minutes("13:45"),
        "avail_end": time_to_minutes("20:15"),
        "duration": 60
    },
    "Margaret": {
        "location": "Presidio",
        "avail_start": time_to_minutes("10:15"),
        "avail_end": time_to_minutes("15:15"),
        "duration": 30
    },
    "Kevin": {
        "location": "Haight-Ashbury",
        "avail_start": time_to_minutes("20:00"),
        "avail_end": time_to_minutes("20:45"),
        "duration": 30
    },
    "Kimberly": {
        "location": "Union Square",
        "avail_start": time_to_minutes("7:45"),
        "avail_end": time_to_minutes("16:45"),
        "duration": 30
    }
}

# Starting parameters
start_location = "Bayview"
start_time = time_to_minutes("9:00")

# We'll brute force all orders of meetings to choose one that meets all constraints.
# We will choose the order that manages to schedule maximum meetings.
def schedule_for_order(order):
    itinerary = []
    curr_time = start_time
    curr_location = start_location
    total_wait = 0
    for person in order:
        friend = friends[person]
        destination = friend["location"]
        # travel time from current location to destination
        travel = travel_times[curr_location][destination]
        arrival_time = curr_time + travel

        # Meeting can only start at max(arrival_time, friend's available start)
        meeting_start = max(arrival_time, friend["avail_start"])
        # If the meeting start time is later than the available window end minus required duration, it's invalid.
        if meeting_start + friend["duration"] > friend["avail_end"]:
            return None  # invalid schedule for this order

        # Calculate waiting time if any (if arrival_time < available start)
        wait = meeting_start - arrival_time
        total_wait += wait

        meeting_end = meeting_start + friend["duration"]

        # Append meeting action to itinerary
        itinerary.append({
            "action": "meet",
            "location": destination,
            "person": person,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })

        # Update current time and location for next leg.
        curr_time = meeting_end
        curr_location = destination
    return {
        "itinerary": itinerary,
        "total_wait": total_wait,
        "end_time": curr_time  # Not used for now but available if needed.
    }

best_schedule = None
best_meetings = -1
best_wait = None

# Try all permutations of friends
for order in itertools.permutations(friends.keys()):
    result = schedule_for_order(order)
    if result is not None:
        num_meetings = len(result["itinerary"])
        if num_meetings > best_meetings:
            best_schedule = result
            best_meetings = num_meetings
            best_wait = result["total_wait"]
        elif num_meetings == best_meetings:
            # Tie-breaker: choose schedule with lower total waiting time.
            if result["total_wait"] < best_wait:
                best_schedule = result
                best_wait = result["total_wait"]

# Output the best schedule in JSON format with the required structure.
if best_schedule is None:
    output = {"itinerary": []}
else:
    output = {"itinerary": best_schedule["itinerary"]}

print(json.dumps(output, indent=2))