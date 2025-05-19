#!/usr/bin/env python3
import json
import copy

# Helper functions to convert time formats
def time_to_minutes(t_str):
    # t_str in format "H:MM" (24-hour) or "H:MMAM/PM"
    # For our use, we'll assume input times are in 24-hour format if no AM/PM
    if t_str[-2:].lower() in ['am','pm']:
        # Convert from e.g., "7:15PM"
        period = t_str[-2:].lower()
        t_core = t_str[:-2]
        hours, minutes = map(int, t_core.split(":"))
        if period == 'pm' and hours != 12:
            hours += 12
        if period == 'am' and hours == 12:
            hours = 0
    else:
        hours, minutes = map(int, t_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Travel times (in minutes) between locations as provided, stored as nested dictionary.
travel_times = {
    "Mission District": {
        "The Castro": 7,
        "Nob Hill": 12,
        "Presidio": 25,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "Chinatown": 16,
        "Richmond District": 20
    },
    "The Castro": {
        "Mission District": 7,
        "Nob Hill": 16,
        "Presidio": 20,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Chinatown": 22,
        "Richmond District": 16
    },
    "Nob Hill": {
        "Mission District": 13,
        "The Castro": 17,
        "Presidio": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Chinatown": 6,
        "Richmond District": 14
    },
    "Presidio": {
        "Mission District": 26,
        "The Castro": 21,
        "Nob Hill": 18,
        "Marina District": 11,
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7
    },
    "Marina District": {
        "Mission District": 20,
        "The Castro": 22,
        "Nob Hill": 12,
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Chinatown": 15,
        "Richmond District": 11
    },
    "Pacific Heights": {
        "Mission District": 15,
        "The Castro": 16,
        "Nob Hill": 8,
        "Presidio": 11,
        "Marina District": 6,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Richmond District": 12
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "The Castro": 13,
        "Nob Hill": 20,
        "Presidio": 11,
        "Marina District": 16,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Richmond District": 7
    },
    "Chinatown": {
        "Mission District": 17,
        "The Castro": 22,
        "Nob Hill": 9,
        "Presidio": 19,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Golden Gate Park": 23,
        "Richmond District": 20
    },
    "Richmond District": {
        "Mission District": 20,
        "The Castro": 16,
        "Nob Hill": 17,
        "Presidio": 7,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Chinatown": 20
    }
}

# Meeting constraints for each friend. Times are stored in minutes after midnight.
meetings = {
    "Lisa": {
        "location": "The Castro",
        "avail_start": time_to_minutes("19:15"),
        "avail_end": time_to_minutes("21:15"),
        "min_duration": 120
    },
    "Daniel": {
        "location": "Nob Hill",
        "avail_start": time_to_minutes("8:15"),
        "avail_end": time_to_minutes("11:00"),
        "min_duration": 15
    },
    "Elizabeth": {
        "location": "Presidio",
        "avail_start": time_to_minutes("21:15"),
        "avail_end": time_to_minutes("22:15"),
        "min_duration": 45
    },
    "Steven": {
        "location": "Marina District",
        "avail_start": time_to_minutes("16:30"),
        "avail_end": time_to_minutes("20:45"),
        "min_duration": 90
    },
    "Timothy": {
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("12:00"),
        "avail_end": time_to_minutes("18:00"),
        "min_duration": 90
    },
    "Ashley": {
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("20:45"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 60
    },
    "Kevin": {
        "location": "Chinatown",
        "avail_start": time_to_minutes("12:00"),
        "avail_end": time_to_minutes("19:00"),
        "min_duration": 30
    },
    "Betty": {
        "location": "Richmond District",
        "avail_start": time_to_minutes("13:15"),
        "avail_end": time_to_minutes("15:45"),
        "min_duration": 30
    }
}

# Initial state parameters
START_TIME = time_to_minutes("9:00")
START_LOCATION = "Mission District"

# We'll use backtracking to search over all possible orders of meetings to maximize number of friends met.
# Each state: current_time, current_location, remaining meetings, current itinerary.
# Itinerary items will be a list of dict items with meeting details.
best_itinerary = []
best_count = 0

def search(curr_time, curr_loc, remaining, itinerary):
    global best_itinerary, best_count
    # Update best if current itinerary length is greater
    if len(itinerary) > best_count:
        best_count = len(itinerary)
        best_itinerary = copy.deepcopy(itinerary)
    # Try each remaining meeting
    for person in list(remaining.keys()):
        meeting = remaining[person]
        dest = meeting["location"]
        # Check if travel time exists from current location to destination
        if curr_loc not in travel_times or dest not in travel_times[curr_loc]:
            continue
        travel = travel_times[curr_loc][dest]
        arrival_time = curr_time + travel
        # meeting can only start at max(arrival_time, meeting available start)
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]
        # Check if meeting can be finished within avail_end
        if meeting_end > meeting["avail_end"]:
            continue
        # Prepare itinerary record for this meeting
        meeting_item = {
            "action": "meet",
            "location": dest,
            "person": person,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        # Create new remaining dictionary without this person
        new_remaining = copy.deepcopy(remaining)
        del new_remaining[person]
        # Recurse from the end time and destination of this meeting
        new_itinerary = itinerary + [meeting_item]
        search(meeting_end, dest, new_remaining, new_itinerary)
    # Also, it's valid to end the itinerary here.

# Run the search starting from the initial state with all meetings available.
search(START_TIME, START_LOCATION, meetings, [])

# Prepare the output dictionary in the required JSON structure.
output = {
    "itinerary": best_itinerary
}

# Output the JSON formatted result.
print(json.dumps(output, indent=2))