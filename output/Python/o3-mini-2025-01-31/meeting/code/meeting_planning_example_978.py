#!/usr/bin/env python3
import json
import copy

# Helper functions to convert time strings (HH:MM) to minutes from midnight and vice versa.
def time_to_minutes(t):
    # t is a string like "9:00" or "15:30"
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # returns string without leading zeros in hour.
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Define travel times as a nested dictionary.
# For each origin and destination we record the travel time in minutes.
# Only the provided entries are included.
travel_times = {
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Financial District": 5,
        "Russian Hill": 8,
        "Marina District": 12,
        "Richmond District": 21,
        "Pacific Heights": 11,
        "Haight-Ashbury": 21,
        "Presidio": 20,
        "Nob Hill": 10,
        "The Castro": 25
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Financial District": 11,
        "Russian Hill": 7,
        "Marina District": 9,
        "Richmond District": 18,
        "Pacific Heights": 12,
        "Haight-Ashbury": 22,
        "Presidio": 17,
        "Nob Hill": 11,
        "The Castro": 27
    },
    "Financial District": {
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
        "Russian Hill": 11,
        "Marina District": 15,
        "Richmond District": 21,
        "Pacific Heights": 13,
        "Haight-Ashbury": 19,
        "Presidio": 22,
        "Nob Hill": 8,
        "The Castro": 20
    },
    "Russian Hill": {
        "Embarcadero": 8,
        "Fisherman's Wharf": 7,
        "Financial District": 11,
        "Marina District": 7,
        "Richmond District": 14,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Presidio": 14,
        "Nob Hill": 5,
        "The Castro": 21
    },
    "Marina District": {
        "Embarcadero": 14,
        "Fisherman's Wharf": 10,
        "Financial District": 17,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Presidio": 10,
        "Nob Hill": 12,
        "The Castro": 22
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 18,
        "Financial District": 22,
        "Russian Hill": 13,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Presidio": 7,
        "Nob Hill": 17,
        "The Castro": 16
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Fisherman's Wharf": 13,
        "Financial District": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "Richmond District": 12,
        "Haight-Ashbury": 11,
        "Presidio": 11,
        "Nob Hill": 8,
        "The Castro": 16
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Financial District": 21,
        "Russian Hill": 17,
        "Marina District": 17,
        "Richmond District": 10,
        "Pacific Heights": 12,
        "Presidio": 15,
        "Nob Hill": 15,
        "The Castro": 6
    },
    "Presidio": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 19,
        "Financial District": 23,
        "Russian Hill": 14,
        "Marina District": 11,
        "Richmond District": 7,
        "Pacific Heights": 11,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "The Castro": 21
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Fisherman's Wharf": 10,
        "Financial District": 9,
        "Russian Hill": 5,
        "Marina District": 11,
        "Richmond District": 14,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Presidio": 17,
        "The Castro": 17
    },
    "The Castro": {
        "Embarcadero": 22,
        "Fisherman's Wharf": 24,
        "Financial District": 21,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Presidio": 20,
        "Nob Hill": 16
    }
}

# Helper function to get travel time between two locations
def get_travel_time(origin, destination):
    if origin == destination:
        return 0
    # If a route isn't found in the dictionary, assume a large travel time.
    return travel_times.get(origin, {}).get(destination, 999)

# Define each meeting constraint as a dictionary.
# Each meeting includes:
#  - person: name of friend
#  - location: meeting location (as in travel_times keys)
#  - avail_start: earliest available time (in minutes from midnight)
#  - avail_end: latest finish time (in minutes)
#  - duration: minimum meeting duration (in minutes)
meetings = [
    {
        "person": "Stephanie",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("15:30"),
        "avail_end": time_to_minutes("22:00"),
        "duration": 30
    },
    {
        "person": "Lisa",
        "location": "Financial District",
        "avail_start": time_to_minutes("10:45"),
        "avail_end": time_to_minutes("17:15"),
        "duration": 15
    },
    {
        "person": "Melissa",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("17:00"),
        "avail_end": time_to_minutes("21:45"),
        "duration": 120
    },
    {
        "person": "Betty",
        "location": "Marina District",
        "avail_start": time_to_minutes("10:45"),
        "avail_end": time_to_minutes("14:15"),
        "duration": 60
    },
    {
        "person": "Sarah",
        "location": "Richmond District",
        "avail_start": time_to_minutes("16:15"),
        "avail_end": time_to_minutes("19:30"),
        "duration": 105
    },
    {
        "person": "Daniel",
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("18:30"),
        "avail_end": time_to_minutes("21:45"),
        "duration": 60
    },
    {
        "person": "Joshua",
        "location": "Haight-Ashbury",
        "avail_start": time_to_minutes("9:00"),
        "avail_end": time_to_minutes("15:30"),
        "duration": 15
    },
    {
        "person": "Joseph",
        "location": "Presidio",
        "avail_start": time_to_minutes("7:00"),
        "avail_end": time_to_minutes("13:00"),
        "duration": 45
    },
    {
        "person": "Andrew",
        "location": "Nob Hill",
        "avail_start": time_to_minutes("19:45"),
        "avail_end": time_to_minutes("22:00"),
        "duration": 105
    },
    {
        "person": "John",
        "location": "The Castro",
        "avail_start": time_to_minutes("13:15"),
        "avail_end": time_to_minutes("19:45"),
        "duration": 45
    }
]

# We want to maximize the count of meetings we can attend.
# We'll use recursion/backtracking to try sequences of meetings that are feasible from a given state.
# The state is defined by current location and current time.
# We start at Embarcadero at 9:00.
start_location = "Embarcadero"
start_time = time_to_minutes("9:00")

# Global variable to store best schedule (maximum count, if tie can choose one).
best_schedule = []
best_count = 0

def search(current_location, current_time, remaining_meetings, schedule):
    global best_schedule, best_count
    # Update best_schedule if current schedule count is higher than best_count.
    if len(schedule) > best_count:
        best_count = len(schedule)
        best_schedule = copy.deepcopy(schedule)
    
    # Try each meeting in the remaining list
    for idx, meeting in enumerate(remaining_meetings):
        travel = get_travel_time(current_location, meeting["location"])
        arrival_time = current_time + travel
        # The meeting cannot start before its available start.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can be finished before the meeting's available end.
        if meeting_end <= meeting["avail_end"]:
            # Create an appointment record.
            appointment = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            # Prepare new remaining list without the current meeting.
            new_remaining = remaining_meetings[:idx] + remaining_meetings[idx+1:]
            # Recurse, note that after finishing this meeting, we may wait for the next meeting.
            search(meeting["location"], meeting_end, new_remaining, schedule + [appointment])
    # End recursion.

# Run the search.
search(start_location, start_time, meetings, [])

# For a realistic day schedule, we want to ensure the itinerary is in chronological order.
# Our search produces an itinerary that is already in order.
result = {"itinerary": best_schedule}

# Output the result as a JSON-formatted dictionary.
print(json.dumps(result, indent=2))
                    
if __name__ == '__main__':
    pass