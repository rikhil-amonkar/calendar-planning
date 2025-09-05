import json

# Helper function to convert minutes to "H:MM" format
def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define the travel times (in minutes) as given.
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

# Define the friends with their meeting constraints.
# Times are in minutes from midnight.
# For example "9:00" -> 9*60 = 540; "10:45" -> 645, etc.
friends = [
    {
        "person": "Stephanie",
        "location": "Fisherman's Wharf",
        "avail_start": 15 * 60 + 30,  # 15:30 -> 930
        "avail_end": 22 * 60,         # 22:00 -> 1320
        "duration": 30
    },
    {
        "person": "Lisa",
        "location": "Financial District",
        "avail_start": 10 * 60 + 45,  # 10:45 -> 645
        "avail_end": 17 * 60 + 15,    # 17:15 -> 1035
        "duration": 15
    },
    {
        "person": "Melissa",
        "location": "Russian Hill",
        "avail_start": 17 * 60,       # 17:00 -> 1020
        "avail_end": 21 * 60 + 45,    # 21:45 -> 1305
        "duration": 120
    },
    {
        "person": "Betty",
        "location": "Marina District",
        "avail_start": 10 * 60 + 45,  # 10:45 -> 645
        "avail_end": 14 * 60 + 15,    # 14:15 -> 855
        "duration": 60
    },
    {
        "person": "Sarah",
        "location": "Richmond District",
        "avail_start": 16 * 60 + 15,  # 16:15 -> 975
        "avail_end": 19 * 60 + 30,    # 19:30 -> 1170
        "duration": 105
    },
    {
        "person": "Daniel",
        "location": "Pacific Heights",
        "avail_start": 18 * 60 + 30,  # 18:30 -> 1110
        "avail_end": 21 * 60 + 45,    # 21:45 -> 1305
        "duration": 60
    },
    {
        "person": "Joshua",
        "location": "Haight-Ashbury",
        "avail_start": 9 * 60,        # 9:00 -> 540
        "avail_end": 15 * 60 + 30,      # 15:30 -> 930
        "duration": 15
    },
    {
        "person": "Joseph",
        "location": "Presidio",
        "avail_start": 7 * 60,        # 7:00 -> 420
        "avail_end": 13 * 60,         # 13:00 -> 780
        "duration": 45
    },
    {
        "person": "Andrew",
        "location": "Nob Hill",
        "avail_start": 19 * 60 + 45,   # 19:45 -> 1185
        "avail_end": 22 * 60,          # 22:00 -> 1320
        "duration": 105
    },
    {
        "person": "John",
        "location": "The Castro",
        "avail_start": 13 * 60 + 15,   # 13:15 -> 795
        "avail_end": 19 * 60 + 45,     # 19:45 -> 1185
        "duration": 45
    }
]

# Recursive backtracking search to compute the optimal schedule.
# The goal is to maximize the number of meetings.
def search(current_time, current_location, remaining, schedule):
    best_schedule = schedule[:]
    for i in range(len(remaining)):
        friend = remaining[i]
        # Get travel time from current_location to friend's meeting location
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if we can finish the meeting before the friend leaves.
        if meeting_end <= friend["avail_end"]:
            meeting = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["person"],
                "start_time": meeting_start,  # will format later
                "end_time": meeting_end       # will format later
            }
            new_schedule = schedule + [meeting]
            new_remaining = remaining[:i] + remaining[i+1:]
            candidate = search(meeting_end, friend["location"], new_remaining, new_schedule)
            if len(candidate) > len(best_schedule):
                best_schedule = candidate
    return best_schedule

# Starting state: Arrive at Embarcadero at 9:00 (540 minutes).
start_time = 9 * 60  # 9:00
start_location = "Embarcadero"

# Compute the optimal schedule
optimal_schedule = search(start_time, start_location, friends, [])

# Format the meeting times for output
for meeting in optimal_schedule:
    meeting["start_time"] = format_time(meeting["start_time"])
    meeting["end_time"] = format_time(meeting["end_time"])

result = {"itinerary": optimal_schedule}
print(json.dumps(result, indent=2))