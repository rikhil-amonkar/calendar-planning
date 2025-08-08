#!/usr/bin/env python3
import json
import copy

# Helper function to convert minutes (since midnight) to "H:MM" 24‐hour format.
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times dictionary (in minutes) for all given pairs.
# Keys: (origin, destination)
travel_times = {
    ("Fisherman's Wharf", "The Castro"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "North Beach"): 6,

    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "North Beach"): 20,

    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Russian Hill"): 21,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "North Beach"): 24,

    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "North Beach"): 5,

    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "North Beach"): 5,

    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "North Beach"): 8,

    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "North Beach"): 15,

    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Alamo Square"): 16
}

def get_travel_time(origin, destination):
    # Return the travel time if defined, else a large number.
    return travel_times.get((origin, destination), 9999)

# Meeting constraints.
# Times are represented as minutes since midnight.
# Arrival: You arrive at Fisherman's Wharf at 9:00 AM (9*60 = 540)
# The input meetings (only those possible given arrival time are considered):
#   Laura: The Castro, available 19:45 (1185) to 21:30 (1290), min duration 105.
#   Daniel: Golden Gate Park, available 21:15 (1275) to 21:45 (1305), min duration 15.
#   Karen: Russian Hill, available 14:30 (870) to 19:45 (1185), min duration 30.
#   Joseph: Alamo Square, available 11:30 (690) to 12:45 (765), min duration 15.
#   Kimberly: North Beach, available 15:45 (945) to 19:15 (1155), min duration 30.
meetings = [
    {
        "person": "Joseph",
        "location": "Alamo Square",
        "avail_start": 690,  # 11:30
        "avail_end": 765,    # 12:45
        "duration": 15
    },
    {
        "person": "Karen",
        "location": "Russian Hill",
        "avail_start": 870,  # 14:30
        "avail_end": 1185,   # 19:45
        "duration": 30
    },
    {
        "person": "Kimberly",
        "location": "North Beach",
        "avail_start": 945,  # 15:45
        "avail_end": 1155,   # 19:15
        "duration": 30
    },
    {
        "person": "Laura",
        "location": "The Castro",
        "avail_start": 1185, # 19:45
        "avail_end": 1290,   # 21:30
        "duration": 105
    },
    {
        "person": "Daniel",
        "location": "Golden Gate Park",
        "avail_start": 1275, # 21:15
        "avail_end": 1305,   # 21:45
        "duration": 15
    }
]

# Global variables to store the best (maximum count) schedule found.
best_schedule = []
best_count = 0

# Recursive function to search for a feasible meeting schedule.
def search_schedule(current_time, current_location, remaining_meetings, current_schedule):
    global best_schedule, best_count
    # Update best schedule if current_schedule has more meetings.
    if len(current_schedule) > best_count:
        best_count = len(current_schedule)
        best_schedule = copy.deepcopy(current_schedule)
    # Try scheduling each remaining meeting next.
    for i, meeting in enumerate(remaining_meetings):
        # Compute arrival time at the candidate meeting's location.
        travel = get_travel_time(current_location, meeting["location"])
        arrival_time = current_time + travel
        # Meeting can only start when the person is available.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can be completed within the availability window.
        if meeting_end <= meeting["avail_end"]:
            event = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }
            new_schedule = current_schedule + [event]
            # Create a new remaining list without the current meeting.
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            search_schedule(meeting_end, meeting["location"], new_remaining, new_schedule)

def main():
    # Starting conditions:
    start_time = 540  # 9:00 AM
    start_location = "Fisherman's Wharf"
    search_schedule(start_time, start_location, meetings, [])
    # Prepare the output JSON dictionary.
    result = {
        "itinerary": best_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()