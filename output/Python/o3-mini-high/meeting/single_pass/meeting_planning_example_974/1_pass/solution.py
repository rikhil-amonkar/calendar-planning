#!/usr/bin/env python3
import json

# Helper functions to convert time formats
def time_to_minutes(time_str):
    # expects time_str in "H:MM" (24-hour format) with no leading zero on hour
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define the travel time matrix as a nested dictionary
travel_times = {
    "Sunset District": {
        "Presidio": 16,
        "Nob Hill": 27,
        "Pacific Heights": 21,
        "Mission District": 25,
        "Marina District": 21,
        "North Beach": 28,
        "Russian Hill": 24,
        "Richmond District": 12,
        "Embarcadero": 30,
        "Alamo Square": 17
    },
    "Presidio": {
        "Sunset District": 15,
        "Nob Hill": 18,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Marina District": 11,
        "North Beach": 18,
        "Russian Hill": 14,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Alamo Square": 19
    },
    "Nob Hill": {
        "Sunset District": 24,
        "Presidio": 17,
        "Pacific Heights": 8,
        "Mission District": 13,
        "Marina District": 11,
        "North Beach": 8,
        "Russian Hill": 5,
        "Richmond District": 14,
        "Embarcadero": 9,
        "Alamo Square": 11
    },
    "Pacific Heights": {
        "Sunset District": 21,
        "Presidio": 11,
        "Nob Hill": 8,
        "Mission District": 15,
        "Marina District": 6,
        "North Beach": 9,
        "Russian Hill": 7,
        "Richmond District": 12,
        "Embarcadero": 10,
        "Alamo Square": 10
    },
    "Mission District": {
        "Sunset District": 24,
        "Presidio": 25,
        "Nob Hill": 12,
        "Pacific Heights": 16,
        "Marina District": 19,
        "North Beach": 17,
        "Russian Hill": 15,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Alamo Square": 11
    },
    "Marina District": {
        "Sunset District": 19,
        "Presidio": 10,
        "Nob Hill": 12,
        "Pacific Heights": 7,
        "Mission District": 20,
        "North Beach": 11,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Alamo Square": 15
    },
    "North Beach": {
        "Sunset District": 27,
        "Presidio": 17,
        "Nob Hill": 7,
        "Pacific Heights": 8,
        "Mission District": 18,
        "Marina District": 9,
        "Russian Hill": 4,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Alamo Square": 16
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Presidio": 14,
        "Nob Hill": 5,
        "Pacific Heights": 7,
        "Mission District": 16,
        "Marina District": 7,
        "North Beach": 5,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Alamo Square": 15
    },
    "Richmond District": {
        "Sunset District": 11,
        "Presidio": 7,
        "Nob Hill": 17,
        "Pacific Heights": 10,
        "Mission District": 20,
        "Marina District": 9,
        "North Beach": 17,
        "Russian Hill": 13,
        "Embarcadero": 19,
        "Alamo Square": 13
    },
    "Embarcadero": {
        "Sunset District": 30,
        "Presidio": 20,
        "Nob Hill": 10,
        "Pacific Heights": 11,
        "Mission District": 20,
        "Marina District": 12,
        "North Beach": 5,
        "Russian Hill": 8,
        "Richmond District": 21,
        "Alamo Square": 19
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Presidio": 17,
        "Nob Hill": 11,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Marina District": 15,
        "North Beach": 15,
        "Russian Hill": 13,
        "Richmond District": 11,
        "Embarcadero": 16
    }
}

# Define meeting constraints as a list of dictionaries.
meetings = [
    {
        "person": "Charles",
        "location": "Presidio",
        "window_start": time_to_minutes("13:15"),
        "window_end": time_to_minutes("15:00"),
        "duration": 105
    },
    {
        "person": "Robert",
        "location": "Nob Hill",
        "window_start": time_to_minutes("13:15"),
        "window_end": time_to_minutes("17:30"),
        "duration": 90
    },
    {
        "person": "Nancy",
        "location": "Pacific Heights",
        "window_start": time_to_minutes("14:45"),
        "window_end": time_to_minutes("22:00"),
        "duration": 105
    },
    {
        "person": "Brian",
        "location": "Mission District",
        "window_start": time_to_minutes("15:30"),
        "window_end": time_to_minutes("22:00"),
        "duration": 60
    },
    {
        "person": "Kimberly",
        "location": "Marina District",
        "window_start": time_to_minutes("17:00"),
        "window_end": time_to_minutes("19:45"),
        "duration": 75
    },
    {
        "person": "David",
        "location": "North Beach",
        "window_start": time_to_minutes("14:45"),
        "window_end": time_to_minutes("16:30"),
        "duration": 75
    },
    {
        "person": "William",
        "location": "Russian Hill",
        "window_start": time_to_minutes("12:30"),
        "window_end": time_to_minutes("19:15"),
        "duration": 120
    },
    {
        "person": "Jeffrey",
        "location": "Richmond District",
        "window_start": time_to_minutes("12:00"),
        "window_end": time_to_minutes("19:15"),
        "duration": 45
    },
    {
        "person": "Karen",
        "location": "Embarcadero",
        "window_start": time_to_minutes("14:15"),
        "window_end": time_to_minutes("20:45"),
        "duration": 60
    },
    {
        "person": "Joshua",
        "location": "Alamo Square",
        "window_start": time_to_minutes("18:45"),
        "window_end": time_to_minutes("22:00"),
        "duration": 60
    }
]

# Global variables to track the best schedule found.
best_schedule = []
best_count = 0

def dfs(current_time, current_loc, scheduled, remaining):
    global best_schedule, best_count
    progressed = False
    # Try to schedule each remaining meeting from the current state.
    for meeting in remaining:
        # Calculate travel time from current location to the meeting's location.
        travel_time = travel_times[current_loc][meeting["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start at the maximum of the arrival time and the meeting's window start.
        meeting_start = max(arrival_time, meeting["window_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can finish within the allowed window.
        if meeting_end <= meeting["window_end"]:
            # Create an itinerary entry for this meeting.
            meeting_entry = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_scheduled = scheduled + [meeting_entry]
            new_remaining = remaining.copy()
            new_remaining.remove(meeting)
            # Continue the search from this new state.
            dfs(meeting_end, meeting["location"], new_scheduled, new_remaining)
            progressed = True
    # If we could not schedule any more meetings, update the best schedule if necessary.
    if not progressed:
        if len(scheduled) > best_count:
            best_schedule = scheduled
            best_count = len(scheduled)

def main():
    # Start at Sunset District at 9:00 AM (9:00 -> 540 minutes)
    start_time = time_to_minutes("9:00")
    start_location = "Sunset District"
    dfs(start_time, start_location, [], meetings)
    
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()