#!/usr/bin/env python3
import json
import itertools

def minutes_to_time_str(minutes):
    # Convert minutes since midnight to H:MM 24-hour format (no leading zero)
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times in minutes between locations
# travel_times[from_location][to_location]
travel_times = {
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Golden Gate Park": 11,
        "Mission District": 24
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Russian Hill": 13,
        "Golden Gate Park": 9,
        "Mission District": 10
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "Mission District": 16
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Alamo Square": 10,
        "Russian Hill": 19,
        "Mission District": 17
    },
    "Mission District": {
        "Sunset District": 24,
        "Alamo Square": 11,
        "Russian Hill": 15,
        "Golden Gate Park": 17
    }
}

# Define participant meeting constraints and available locations, times in minutes since midnight
# You arrive at Sunset District at 9:00 (540 minutes).
participants = {
    "Charles": {
        "location": "Alamo Square",
        "avail_start": 18 * 60,        # 18:00 -> 1080
        "avail_end": 20 * 60 + 45,      # 20:45 -> 1245
        "duration": 90
    },
    "Margaret": {
        "location": "Russian Hill",
        "avail_start": 9 * 60,         # 9:00 -> 540
        "avail_end": 16 * 60,          # 16:00 -> 960
        "duration": 30
    },
    "Daniel": {
        "location": "Golden Gate Park",
        "avail_start": 8 * 60,         # 8:00 -> 480
        "avail_end": 13 * 60 + 30,     # 13:30 -> 810
        "duration": 15
    },
    "Stephanie": {
        "location": "Mission District",
        "avail_start": 20 * 60 + 30,   # 20:30 -> 1230
        "avail_end": 22 * 60,          # 22:00 -> 1320
        "duration": 90
    }
}

# The meetings are divided into two parts:
# Morning meetings: Daniel and Margaret can be scheduled in either order (they must finish by their avail_end).
# Evening meetings: Charles then Stephanie (their time windows force this order).
morning_names = ["Daniel", "Margaret"]
evening_names = ["Charles", "Stephanie"]

# Starting point and time:
start_location = "Sunset District"
start_time = 9 * 60  # 9:00 AM

def simulate_schedule(morning_order):
    itinerary = []
    current_location = start_location
    current_time = start_time

    # Process morning meetings (Daniel and Margaret in the given order)
    for name in morning_order:
        person = participants[name]
        meeting_location = person["location"]
        # Travel to meeting location
        travel_time = travel_times[current_location][meeting_location]
        arrival_time = current_time + travel_time
        # Meeting starts at the later of arrival time and person's available start
        meeting_start = max(arrival_time, person["avail_start"])
        meeting_end = meeting_start + person["duration"]
        # Check if meeting can finish before person's available end
        if meeting_end > person["avail_end"]:
            return None  # invalid schedule
        itinerary.append({
            "action": "meet",
            "location": meeting_location,
            "person": name,
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        current_location = meeting_location
        current_time = meeting_end

    # Process evening meetings in fixed order: Charles then Stephanie
    # For Charles:
    name = "Charles"
    person = participants[name]
    meeting_location = person["location"]
    travel_time = travel_times[current_location][meeting_location]
    arrival_time = current_time + travel_time
    meeting_start = max(arrival_time, person["avail_start"])
    meeting_end = meeting_start + person["duration"]
    if meeting_end > person["avail_end"]:
        return None
    itinerary.append({
        "action": "meet",
        "location": meeting_location,
        "person": name,
        "start_time": minutes_to_time_str(meeting_start),
        "end_time": minutes_to_time_str(meeting_end)
    })
    current_location = meeting_location
    current_time = meeting_end

    # For Stephanie:
    name = "Stephanie"
    person = participants[name]
    meeting_location = person["location"]
    travel_time = travel_times[current_location][meeting_location]
    arrival_time = current_time + travel_time
    meeting_start = max(arrival_time, person["avail_start"])
    meeting_end = meeting_start + person["duration"]
    if meeting_end > person["avail_end"]:
        return None
    itinerary.append({
        "action": "meet",
        "location": meeting_location,
        "person": name,
        "start_time": minutes_to_time_str(meeting_start),
        "end_time": minutes_to_time_str(meeting_end)
    })
    # Successful schedule, also include overall itinerary data
    return itinerary

# Try all possible orders for morning meetings and select the best valid schedule.
valid_schedules = []
for order in itertools.permutations(morning_names):
    schedule = simulate_schedule(order)
    if schedule is not None:
        # Compute finish time (in minutes) of the last meeting
        last_meeting = schedule[-1]
        # Convert end_time string to minutes
        end_hour, end_min = map(int, last_meeting["end_time"].split(":"))
        finish_time = end_hour * 60 + end_min
        valid_schedules.append((finish_time, order, schedule))

# Select the schedule with the earliest finishing time (optimal in terms of time)
if valid_schedules:
    valid_schedules.sort(key=lambda x: x[0])
    best_schedule = valid_schedules[0][2]
else:
    best_schedule = []

# Prepare output in JSON format
output = {"itinerary": best_schedule}
print(json.dumps(output))