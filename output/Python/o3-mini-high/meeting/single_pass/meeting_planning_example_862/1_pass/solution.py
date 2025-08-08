#!/usr/bin/env python3
import json
import copy

# Helper functions for time conversion
def time_to_minutes(time_str):
    # Assumes format "H:MM" in 24-hour time
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # Convert minutes since midnight to "H:MM" (no leading zero for hour)
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

# Define travel times (in minutes) as a nested dictionary
travel_times = {
    "Mission District": {
        "Alamo Square": 11,
        "Presidio": 25,
        "Russian Hill": 15,
        "North Beach": 17,
        "Golden Gate Park": 17,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Financial District": 15,
        "Marina District": 19
    },
    "Alamo Square": {
        "Mission District": 10,
        "Presidio": 17,
        "Russian Hill": 13,
        "North Beach": 15,
        "Golden Gate Park": 9,
        "Richmond District": 11,
        "Embarcadero": 16,
        "Financial District": 17,
        "Marina District": 15
    },
    "Presidio": {
        "Mission District": 26,
        "Alamo Square": 19,
        "Russian Hill": 14,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Financial District": 23,
        "Marina District": 11
    },
    "Russian Hill": {
        "Mission District": 16,
        "Alamo Square": 15,
        "Presidio": 14,
        "North Beach": 5,
        "Golden Gate Park": 21,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Financial District": 11,
        "Marina District": 7
    },
    "North Beach": {
        "Mission District": 18,
        "Alamo Square": 16,
        "Presidio": 17,
        "Russian Hill": 4,
        "Golden Gate Park": 22,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Financial District": 8,
        "Marina District": 9
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "Alamo Square": 9,
        "Presidio": 11,
        "Russian Hill": 19,
        "North Beach": 23,
        "Richmond District": 7,
        "Embarcadero": 25,
        "Financial District": 26,
        "Marina District": 16
    },
    "Richmond District": {
        "Mission District": 20,
        "Alamo Square": 13,
        "Presidio": 7,
        "Russian Hill": 13,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "Marina District": 9
    },
    "Embarcadero": {
        "Mission District": 20,
        "Alamo Square": 19,
        "Presidio": 20,
        "Russian Hill": 8,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Richmond District": 21,
        "Financial District": 5,
        "Marina District": 12
    },
    "Financial District": {
        "Mission District": 17,
        "Alamo Square": 17,
        "Presidio": 22,
        "Russian Hill": 11,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Richmond District": 21,
        "Embarcadero": 4,
        "Marina District": 15
    },
    "Marina District": {
        "Mission District": 20,
        "Alamo Square": 15,
        "Presidio": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Financial District": 17
    }
}

# Define meeting constraints.
# Times are stored as minutes since midnight.
# Each meeting is a dict with:
#   person, location, available_start, available_end, duration (in minutes)
meetings = [
    {
        "person": "Laura",
        "location": "Alamo Square",
        "start_window": time_to_minutes("14:30"),
        "end_window": time_to_minutes("16:15"),
        "duration": 75
    },
    {
        "person": "Brian",
        "location": "Presidio",
        "start_window": time_to_minutes("10:15"),
        "end_window": time_to_minutes("17:00"),
        "duration": 30
    },
    {
        "person": "Karen",
        "location": "Russian Hill",
        "start_window": time_to_minutes("18:00"),
        "end_window": time_to_minutes("20:15"),
        "duration": 90
    },
    {
        "person": "Stephanie",
        "location": "North Beach",
        "start_window": time_to_minutes("10:15"),
        "end_window": time_to_minutes("16:00"),
        "duration": 75
    },
    {
        "person": "Helen",
        "location": "Golden Gate Park",
        "start_window": time_to_minutes("11:30"),
        "end_window": time_to_minutes("21:45"),
        "duration": 120
    },
    {
        "person": "Sandra",
        "location": "Richmond District",
        "start_window": time_to_minutes("8:00"),
        "end_window": time_to_minutes("15:15"),
        "duration": 30
    },
    {
        "person": "Mary",
        "location": "Embarcadero",
        "start_window": time_to_minutes("16:45"),
        "end_window": time_to_minutes("18:45"),
        "duration": 120
    },
    {
        "person": "Deborah",
        "location": "Financial District",
        "start_window": time_to_minutes("19:00"),
        "end_window": time_to_minutes("20:45"),
        "duration": 105
    },
    {
        "person": "Elizabeth",
        "location": "Marina District",
        "start_window": time_to_minutes("8:30"),
        "end_window": time_to_minutes("13:15"),
        "duration": 105
    }
]

# We want to maximize number of meetings in the schedule.
# Since not all 9 can be feasibly scheduled (due to overlapping time windows and travel),
# our algorithm will try all orders (backtracking) and save the best schedule (highest count).
best_schedule = []
best_count = 0

def search(current_time, current_location, remaining_meetings, current_schedule):
    global best_schedule, best_count

    # Update best solution if current schedule is longer than the best found so far.
    if len(current_schedule) > best_count:
        best_count = len(current_schedule)
        best_schedule = copy.deepcopy(current_schedule)

    # Try each remaining meeting in turn.
    for i, meeting in enumerate(remaining_meetings):
        # Check if travel is possible from current_location to meeting's location.
        if current_location not in travel_times or meeting["location"] not in travel_times[current_location]:
            # if travel time not defined, skip meeting.
            continue
        travel_time = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start after its available start time.
        start_meet = max(arrival_time, meeting["start_window"])
        end_meet = start_meet + meeting["duration"]
        # Check if meeting can be completed within the availability window.
        if end_meet <= meeting["end_window"]:
            # Create a new schedule entry: store meeting info and start/end times.
            schedule_entry = {
                "person": meeting["person"],
                "location": meeting["location"],
                "start": start_meet,
                "end": end_meet
            }
            new_schedule = current_schedule + [schedule_entry]
            # Remove the meeting from remaining list for recursion.
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            # Recurse with updated state.
            search(end_meet, meeting["location"], new_remaining, new_schedule)

# Starting state: Arrive at Mission District at 9:00 (540 minutes)
initial_time = time_to_minutes("9:00")
initial_location = "Mission District"

# We want to try all orders, so call search with full meetings list.
search(initial_time, initial_location, meetings, [])

# For better results, if there are multiple schedules with the same maximum count, 
# one might choose one with the earliest finish time. Here we simply output the best found schedule.

# Format the best schedule into the required JSON structure.
itinerary = []
for entry in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": entry["location"],
        "person": entry["person"],
        "start_time": minutes_to_time(entry["start"]),
        "end_time": minutes_to_time(entry["end"])
    })

result = {"itinerary": itinerary}

# Output the result as JSON.
print(json.dumps(result, indent=2))
  
if __name__ == '__main__':
    pass