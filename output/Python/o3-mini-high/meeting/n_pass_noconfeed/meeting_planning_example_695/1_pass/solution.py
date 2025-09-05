import json

# Helper function to convert minutes (since midnight) to H:MM (24-hour with no leading zero for hour)
def minutes_to_timestr(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define the travel times as a dictionary-of-dictionaries
travel_times = {
    "Bayview": {
        "Nob Hill": 20,
        "Union Square": 17,
        "Chinatown": 18,
        "The Castro": 20,
        "Presidio": 31,
        "Pacific Heights": 23,
        "Russian Hill": 23
    },
    "Nob Hill": {
        "Bayview": 19,
        "Union Square": 7,
        "Chinatown": 6,
        "The Castro": 17,
        "Presidio": 17,
        "Pacific Heights": 8,
        "Russian Hill": 5
    },
    "Union Square": {
        "Bayview": 15,
        "Nob Hill": 9,
        "Chinatown": 7,
        "The Castro": 19,
        "Presidio": 24,
        "Pacific Heights": 15,
        "Russian Hill": 13
    },
    "Chinatown": {
        "Bayview": 22,
        "Nob Hill": 8,
        "Union Square": 7,
        "The Castro": 22,
        "Presidio": 19,
        "Pacific Heights": 10,
        "Russian Hill": 7
    },
    "The Castro": {
        "Bayview": 19,
        "Nob Hill": 16,
        "Union Square": 19,
        "Chinatown": 20,
        "Presidio": 20,
        "Pacific Heights": 16,
        "Russian Hill": 18
    },
    "Presidio": {
        "Bayview": 31,
        "Nob Hill": 18,
        "Union Square": 22,
        "Chinatown": 21,
        "The Castro": 21,
        "Pacific Heights": 11,
        "Russian Hill": 14
    },
    "Pacific Heights": {
        "Bayview": 22,
        "Nob Hill": 8,
        "Union Square": 12,
        "Chinatown": 11,
        "The Castro": 16,
        "Presidio": 11,
        "Russian Hill": 7
    },
    "Russian Hill": {
        "Bayview": 23,
        "Nob Hill": 5,
        "Union Square": 11,
        "Chinatown": 9,
        "The Castro": 21,
        "Presidio": 14,
        "Pacific Heights": 7
    }
}

# Define friends (each with available time window in minutes from midnight and required meeting duration)
# Times: 9:00 is 540; available times are computed accordingly.
# Paul: at Nob Hill from 16:15 (975) to 21:15 (1275); duration 60
# Carol: at Union Square from 18:00 (1080) to 20:15 (1215); duration 120
# Patricia: at Chinatown from 20:00 (1200) to 21:30 (1290); duration 75
# Karen: at The Castro from 17:00 (1020) to 19:00 (1140); duration 45
# Nancy: at Presidio from 11:45 (705) to 22:00 (1320); duration 30
# Jeffrey: at Pacific Heights from 20:00 (1200) to 20:45 (1245); duration 45
# Matthew: at Russian Hill from 15:45 (945) to 21:45 (1305); duration 75
friends = [
    {"person": "Paul", "location": "Nob Hill", "start": 975, "end": 1275, "duration": 60},
    {"person": "Carol", "location": "Union Square", "start": 1080, "end": 1215, "duration": 120},
    {"person": "Patricia", "location": "Chinatown", "start": 1200, "end": 1290, "duration": 75},
    {"person": "Karen", "location": "The Castro", "start": 1020, "end": 1140, "duration": 45},
    {"person": "Nancy", "location": "Presidio", "start": 705, "end": 1320, "duration": 30},
    {"person": "Jeffrey", "location": "Pacific Heights", "start": 1200, "end": 1245, "duration": 45},
    {"person": "Matthew", "location": "Russian Hill", "start": 945, "end": 1305, "duration": 75}
]

# Backtracking DFS to try all possible meeting orders that satisfy travel and time-window constraints.
# current_time is in minutes from midnight, current_location is the last location.
# remaining: list of friend dictionaries not yet scheduled.
# schedule: list of meetings scheduled so far (each meeting with person, location, start and end in minutes).
def dfs(current_time, current_location, remaining, schedule):
    best_schedule = schedule
    for i, friend in enumerate(remaining):
        # Calculate travel time from current location to friend's location
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # Waiting until friend is available if necessary
        meeting_start = max(arrival_time, friend["start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if the meeting can be completed within friend's availability window
        if meeting_end <= friend["end"]:
            new_meeting = {
                "person": friend["person"],
                "location": friend["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            new_schedule = schedule + [new_meeting]
            # Remove the current friend from the remaining list
            new_remaining = remaining[:i] + remaining[i+1:]
            candidate = dfs(meeting_end, friend["location"], new_remaining, new_schedule)
            if len(candidate) > len(best_schedule):
                best_schedule = candidate
    return best_schedule

# Starting state:
# You arrive at Bayview at 9:00 which is 540 minutes.
start_time = 540
start_location = "Bayview"

# Compute the best schedule (maximizing number of meetings)
best = dfs(start_time, start_location, friends, [])

# Build the output itinerary using the required JSON format.
# Each meeting record must include "action", "location", "person", "start_time", and "end_time".
itinerary = []
for meeting in best:
    itinerary.append({
        "action": "meet",
        "location": meeting["location"],
        "person": meeting["person"],
        "start_time": minutes_to_timestr(meeting["start"]),
        "end_time": minutes_to_timestr(meeting["end"])
    })

output = {"itinerary": itinerary}

# Output the result as a JSON-formatted dictionary
print(json.dumps(output, indent=2))