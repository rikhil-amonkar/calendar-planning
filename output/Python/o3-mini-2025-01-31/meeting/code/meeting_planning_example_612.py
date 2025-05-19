#!/usr/bin/env python3
import json
import copy

# Convert time string H:MM (24-hour) to minutes since midnight
def time_to_minutes(timestr):
    h, m = timestr.split(":")
    return int(h) * 60 + int(m)

# Convert minutes since midnight to time string in H:MM format (no leading zero for hour)
def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes between locations
travel_times = {
    "Alamo Square": {
        "Russian Hill": 13,
        "Presidio": 18,
        "Chinatown": 16,
        "Sunset District": 16,
        "The Castro": 8,
        "Embarcadero": 17,
        "Golden Gate Park": 9,
    },
    "Russian Hill": {
        "Alamo Square": 15,
        "Presidio": 14,
        "Chinatown": 9,
        "Sunset District": 23,
        "The Castro": 21,
        "Embarcadero": 8,
        "Golden Gate Park": 21,
    },
    "Presidio": {
        "Alamo Square": 18,
        "Russian Hill": 14,
        "Chinatown": 21,
        "Sunset District": 15,
        "The Castro": 21,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
    },
    "Chinatown": {
        "Alamo Square": 17,
        "Russian Hill": 7,
        "Presidio": 19,
        "Sunset District": 29,
        "The Castro": 22,
        "Embarcadero": 5,
        "Golden Gate Park": 23,
    },
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Presidio": 16,
        "Chinatown": 30,
        "The Castro": 17,
        "Embarcadero": 31,
        "Golden Gate Park": 11,
    },
    "The Castro": {
        "Alamo Square": 8,
        "Russian Hill": 18,
        "Presidio": 20,
        "Chinatown": 20,
        "Sunset District": 17,
        "Embarcadero": 22,
        "Golden Gate Park": 11,
    },
    "Embarcadero": {
        "Alamo Square": 19,
        "Russian Hill": 8,
        "Presidio": 20,
        "Chinatown": 7,
        "Sunset District": 30,
        "The Castro": 25,
        "Golden Gate Park": 25,
    },
    "Golden Gate Park": {
        "Alamo Square": 10,
        "Russian Hill": 19,
        "Presidio": 11,
        "Chinatown": 23,
        "Sunset District": 10,
        "The Castro": 13,
        "Embarcadero": 25,
    }
}

# Meeting constraints as a list of dictionaries; times in minutes since midnight.
# Times are given in 24-hour format.
meetings = [
    {
        "person": "Emily",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("12:15"),
        "avail_end": time_to_minutes("14:15"),
        "duration": 105
    },
    {
        "person": "Mark",
        "location": "Presidio",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("19:30"),
        "duration": 60
    },
    {
        "person": "Deborah",
        "location": "Chinatown",
        "avail_start": time_to_minutes("7:30"),
        "avail_end": time_to_minutes("15:30"),
        "duration": 45
    },
    {
        "person": "Margaret",
        "location": "Sunset District",
        "avail_start": time_to_minutes("21:30"),
        "avail_end": time_to_minutes("22:30"),
        "duration": 60
    },
    {
        "person": "George",
        "location": "The Castro",
        "avail_start": time_to_minutes("7:30"),
        "avail_end": time_to_minutes("14:15"),
        "duration": 60
    },
    {
        "person": "Andrew",
        "location": "Embarcadero",
        "avail_start": time_to_minutes("20:15"),
        "avail_end": time_to_minutes("22:00"),
        "duration": 75
    },
    {
        "person": "Steven",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("11:15"),
        "avail_end": time_to_minutes("21:15"),
        "duration": 105
    }
]

# Global variable to hold the best schedule (max number of meetings)
best_schedule = []
best_count = 0

def backtrack(current_time, current_location, remaining_meetings, schedule):
    global best_schedule, best_count

    # Update best_schedule if this schedule has more meetings
    if len(schedule) > best_count:
        best_schedule = copy.deepcopy(schedule)
        best_count = len(schedule)

    # Try to add each remaining meeting if feasible
    for i, meeting in enumerate(remaining_meetings):
        # Get travel time from current_location to meeting's location.
        if current_location == meeting["location"]:
            travel = 0
        else:
            # For travel times, if current location not in our travel_times (for instance starting from Alamo Square)
            # We assume the provided dictionary covers all movements from any of the known locations.
            if current_location in travel_times and meeting["location"] in travel_times[current_location]:
                travel = travel_times[current_location][meeting["location"]]
            else:
                # In case location is not found, skip
                continue

        arrival_time = current_time + travel
        # The meeting can only start at max(arrival_time, available start)
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]

        # Check if meeting can be completed within availability window.
        if meeting_end > meeting["avail_end"]:
            continue  # Not feasible

        # Create a new scheduled entry
        scheduled_entry = {
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": meeting_start,
            "end_time": meeting_end
        }

        # Append to schedule and remove this meeting from remaining list.
        new_schedule = schedule + [scheduled_entry]
        new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
        # Recurse with updated current time and location.
        backtrack(meeting_end, meeting["location"], new_remaining, new_schedule)

# Starting conditions:
# You arrive at Alamo Square at 9:00AM, which is 9*60 = 540 minutes.
start_time = time_to_minutes("9:00")
start_location = "Alamo Square"

# Run backtracking search for feasible meeting schedules.
backtrack(start_time, start_location, meetings, [])

# Since our goal is to meet as many friends as possible, we output the best_schedule.
# However, we want to output times in H:MM format.
itinerary = []
for entry in best_schedule:
    itinerary.append({
        "action": entry["action"],
        "location": entry["location"],
        "person": entry["person"],
        "start_time": minutes_to_time(entry["start_time"]),
        "end_time": minutes_to_time(entry["end_time"])
    })

output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))