#!/usr/bin/env python3
import json
import sys

# Helper function to convert minutes (since midnight) to a 24-hour H:MM string.
def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes) between locations.
travel_times = {
    "Marina District": {
        "Embarcadero": 14,
        "Bayview": 27,
        "Union Square": 16,
        "Chinatown": 15,
        "Sunset District": 19,
        "Golden Gate Park": 18,
        "Financial District": 17,
        "Haight-Ashbury": 16,
        "Mission District": 20,
    },
    "Embarcadero": {
        "Marina District": 12,
        "Bayview": 21,
        "Union Square": 10,
        "Chinatown": 7,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Financial District": 5,
        "Haight-Ashbury": 21,
        "Mission District": 20,
    },
    "Bayview": {
        "Marina District": 27,
        "Embarcadero": 19,
        "Union Square": 18,
        "Chinatown": 19,
        "Sunset District": 23,
        "Golden Gate Park": 22,
        "Financial District": 19,
        "Haight-Ashbury": 19,
        "Mission District": 13,
    },
    "Union Square": {
        "Marina District": 18,
        "Embarcadero": 11,
        "Bayview": 15,
        "Chinatown": 7,
        "Sunset District": 27,
        "Golden Gate Park": 22,
        "Financial District": 9,
        "Haight-Ashbury": 18,
        "Mission District": 14,
    },
    "Chinatown": {
        "Marina District": 12,
        "Embarcadero": 5,
        "Bayview": 20,
        "Union Square": 7,
        "Sunset District": 29,
        "Golden Gate Park": 23,
        "Financial District": 5,
        "Haight-Ashbury": 19,
        "Mission District": 17,
    },
    "Sunset District": {
        "Marina District": 21,
        "Embarcadero": 30,
        "Bayview": 22,
        "Union Square": 30,
        "Chinatown": 30,
        "Golden Gate Park": 11,
        "Financial District": 30,
        "Haight-Ashbury": 15,
        "Mission District": 25,
    },
    "Golden Gate Park": {
        "Marina District": 16,
        "Embarcadero": 25,
        "Bayview": 23,
        "Union Square": 22,
        "Chinatown": 23,
        "Sunset District": 10,
        "Financial District": 26,
        "Haight-Ashbury": 7,
        "Mission District": 17,
    },
    "Financial District": {
        "Marina District": 15,
        "Embarcadero": 4,
        "Bayview": 19,
        "Union Square": 9,
        "Chinatown": 5,
        "Sunset District": 30,
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Mission District": 17,
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Embarcadero": 20,
        "Bayview": 18,
        "Union Square": 19,
        "Chinatown": 19,
        "Sunset District": 15,
        "Golden Gate Park": 7,
        "Financial District": 21,
        "Mission District": 11,
    },
    "Mission District": {
        "Marina District": 19,
        "Embarcadero": 19,
        "Bayview": 14,
        "Union Square": 15,
        "Chinatown": 16,
        "Sunset District": 24,
        "Golden Gate Park": 17,
        "Financial District": 15,
        "Haight-Ashbury": 12,
    },
}

# Meeting constraints.
# Times are stored as minutes after midnight.
meetings = [
    {
        "person": "Joshua",
        "location": "Embarcadero",
        "available_start": 9 * 60 + 45,   # 9:45
        "available_end": 18 * 60,         # 18:00
        "duration": 105
    },
    {
        "person": "Jeffrey",
        "location": "Bayview",
        "available_start": 9 * 60 + 45,   # 9:45
        "available_end": 20 * 60 + 15,    # 20:15
        "duration": 75
    },
    {
        "person": "Charles",
        "location": "Union Square",
        "available_start": 10 * 60 + 45,  # 10:45
        "available_end": 20 * 60 + 15,    # 20:15
        "duration": 120
    },
    {
        "person": "Joseph",
        "location": "Chinatown",
        "available_start": 7 * 60,        # 7:00
        "available_end": 15 * 60 + 30,     # 15:30
        "duration": 60
    },
    {
        "person": "Elizabeth",
        "location": "Sunset District",
        "available_start": 9 * 60,        # 9:00
        "available_end": 9 * 60 + 45,      # 9:45
        "duration": 45
    },
    {
        "person": "Matthew",
        "location": "Golden Gate Park",
        "available_start": 11 * 60,       # 11:00
        "available_end": 19 * 60 + 30,    # 19:30
        "duration": 45
    },
    {
        "person": "Carol",
        "location": "Financial District",
        "available_start": 10 * 60 + 45,  # 10:45
        "available_end": 11 * 60 + 15,    # 11:15
        "duration": 15
    },
    {
        "person": "Paul",
        "location": "Haight-Ashbury",
        "available_start": 19 * 60 + 15,  # 19:15
        "available_end": 20 * 60 + 30,    # 20:30
        "duration": 15
    },
    {
        "person": "Rebecca",
        "location": "Mission District",
        "available_start": 17 * 60,       # 17:00
        "available_end": 21 * 60 + 45,    # 21:45
        "duration": 45
    },
]

# Start at Marina District at 9:00
start_location = "Marina District"
start_time = 9 * 60  # 9:00 in minutes

# Global variable to store the best itinerary (maximum number of meetings)
best_schedule = []

# Recursive backtracking function to search for a schedule.
def search(curr_location, curr_time, remaining_meetings, current_schedule):
    global best_schedule
    # Update global best if current schedule has more meetings.
    if len(current_schedule) > len(best_schedule):
        best_schedule = current_schedule.copy()

    # Try to add each remaining meeting if feasible.
    for idx, meeting in enumerate(remaining_meetings):
        # Get the travel time from current location to the meeting's location.
        travel = travel_times[curr_location].get(meeting["location"], sys.maxsize)
        arrival_time = curr_time + travel
        # You cannot start before the meeting’s available start.
        meeting_start = max(arrival_time, meeting["available_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can be completed within its available window.
        if meeting_end <= meeting["available_end"]:
            # Create a scheduled event for this meeting.
            scheduled_event = {
                "person": meeting["person"],
                "location": meeting["location"],
                "start": meeting_start,
                "end": meeting_end,
            }
            next_schedule = current_schedule + [scheduled_event]
            # Exclude the current meeting and proceed recursively.
            new_remaining = remaining_meetings[:idx] + remaining_meetings[idx+1:]
            search(meeting["location"], meeting_end, new_remaining, next_schedule)

# Start the search with the initial state.
search(start_location, start_time, meetings, [])

# Format the best_schedule into the required JSON output structure.
itinerary = []
for event in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": event["location"],
        "person": event["person"],
        "start_time": format_time(event["start"]),
        "end_time": format_time(event["end"])
    })

output = {"itinerary": itinerary}

# Print JSON output.
print(json.dumps(output, indent=2))