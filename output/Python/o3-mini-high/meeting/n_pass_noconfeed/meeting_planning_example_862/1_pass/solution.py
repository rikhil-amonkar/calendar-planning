#!/usr/bin/env python3
import json
import copy

# Helper function to convert minutes (from midnight) to H:MM 24-hour format
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define the travel times between locations (in minutes)
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

# Define the meeting constraints.
# Times are stored as minutes from midnight.
# Each meeting has an earliest available time ("start"), a latest finishing time ("end"), and a minimum meeting duration.
meetings = [
    {
        "person": "Laura",
        "location": "Alamo Square",
        "start": 14 * 60 + 30,  # 14:30 -> 870
        "end": 16 * 60 + 15,    # 16:15 -> 975
        "duration": 75
    },
    {
        "person": "Brian",
        "location": "Presidio",
        "start": 10 * 60 + 15,  # 10:15 -> 615
        "end": 17 * 60 + 0,     # 17:00 -> 1020
        "duration": 30
    },
    {
        "person": "Karen",
        "location": "Russian Hill",
        "start": 18 * 60 + 0,   # 18:00 -> 1080
        "end": 20 * 60 + 15,    # 20:15 -> 1215
        "duration": 90
    },
    {
        "person": "Stephanie",
        "location": "North Beach",
        "start": 10 * 60 + 15,  # 10:15 -> 615
        "end": 16 * 60 + 0,     # 16:00 -> 960
        "duration": 75
    },
    {
        "person": "Helen",
        "location": "Golden Gate Park",
        "start": 11 * 60 + 30,  # 11:30 -> 690
        "end": 21 * 60 + 45,    # 21:45 -> 1305
        "duration": 120
    },
    {
        "person": "Sandra",
        "location": "Richmond District",
        "start": 8 * 60 + 0,    # 8:00 -> 480
        "end": 15 * 60 + 15,    # 15:15 -> 915
        "duration": 30
    },
    {
        "person": "Mary",
        "location": "Embarcadero",
        "start": 16 * 60 + 45,  # 16:45 -> 1005
        "end": 18 * 60 + 45,    # 18:45 -> 1125
        "duration": 120
    },
    {
        "person": "Deborah",
        "location": "Financial District",
        "start": 19 * 60 + 0,   # 19:00 -> 1140
        "end": 20 * 60 + 45,    # 20:45 -> 1245
        "duration": 105
    },
    {
        "person": "Elizabeth",
        "location": "Marina District",
        "start": 8 * 60 + 30,   # 8:30 -> 510
        "end": 13 * 60 + 15,    # 13:15 -> 795
        "duration": 105
    }
]

# Global variable to store the best schedule found
best_schedule = []

# DFS search: state is current location, current time, and available meetings
def dfs(current_loc, current_time, remaining_meetings, schedule):
    global best_schedule
    # Update best_schedule if current schedule has more meetings
    if len(schedule) > len(best_schedule):
        best_schedule = copy.deepcopy(schedule)

    # Try each remaining meeting as next candidate
    for i, meet in enumerate(remaining_meetings):
        # Calculate travel time from current location to meeting location
        if current_loc not in travel_times or meet["location"] not in travel_times[current_loc]:
            continue
        travel = travel_times[current_loc][meet["location"]]
        arrival_time = current_time + travel
        # The meeting can only start after the meeting's available start time.
        meeting_start = max(arrival_time, meet["start"])
        meeting_end = meeting_start + meet["duration"]
        # Check if the meeting can be finished within the available window.
        if meeting_end <= meet["end"]:
            # Create a record of this scheduled meeting
            meeting_record = {
                "person": meet["person"],
                "location": meet["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            # Prepare the new list of remaining meetings (remove the one just scheduled)
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            dfs(meet["location"], meeting_end, new_remaining, schedule + [meeting_record])
    # If no more meetings can be scheduled, this branch ends.

if __name__ == '__main__':
    # Starting state: we arrive at Mission District at 9:00 AM (9*60 = 540 minutes)
    start_location = "Mission District"
    start_time = 9 * 60  # 540 minutes

    dfs(start_location, start_time, meetings, [])

    # Prepare the itinerary in the required JSON structure.
    itinerary = []
    for entry in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": entry["location"],
            "person": entry["person"],
            "start_time": format_time(entry["start"]),
            "end_time": format_time(entry["end"])
        })

    result = {
        "itinerary": itinerary
    }

    print(json.dumps(result, indent=2))