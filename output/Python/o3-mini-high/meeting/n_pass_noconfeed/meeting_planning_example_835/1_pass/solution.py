import json

# Convert time in minutes (from midnight) to "H:MM" format
def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times (in minutes) between locations (non-symmetric)
travel_times = {
    "Pacific Heights": {
        "Golden Gate Park": 15,
        "The Castro": 16,
        "Bayview": 22,
        "Marina District": 6,
        "Union Square": 12,
        "Sunset District": 21,
        "Alamo Square": 10,
        "Financial District": 13,
        "Mission District": 15
    },
    "Golden Gate Park": {
        "Pacific Heights": 16,
        "The Castro": 13,
        "Bayview": 23,
        "Marina District": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "Mission District": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Marina District": 21,
        "Union Square": 19,
        "Sunset District": 17,
        "Alamo Square": 8,
        "Financial District": 21,
        "Mission District": 7
    },
    "Bayview": {
        "Pacific Heights": 23,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Marina District": 27,
        "Union Square": 18,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "Mission District": 13
    },
    "Marina District": {
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Union Square": 16,
        "Sunset District": 19,
        "Alamo Square": 15,
        "Financial District": 17,
        "Mission District": 20
    },
    "Union Square": {
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "The Castro": 17,
        "Bayview": 15,
        "Marina District": 18,
        "Sunset District": 27,
        "Alamo Square": 15,
        "Financial District": 9,
        "Mission District": 14
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Marina District": 21,
        "Union Square": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "Mission District": 25
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Marina District": 15,
        "Union Square": 14,
        "Sunset District": 16,
        "Financial District": 17,
        "Mission District": 10
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Marina District": 15,
        "Union Square": 9,
        "Sunset District": 30,
        "Alamo Square": 17,
        "Mission District": 17
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "The Castro": 7,
        "Bayview": 14,
        "Marina District": 19,
        "Union Square": 15,
        "Sunset District": 24,
        "Alamo Square": 11,
        "Financial District": 15
    }
}

# Meeting constraints.
# Times are represented in minutes from midnight.
# Arrival at Pacific Heights at 9:00 AM => 540 minutes.
meetings = [
    {
        "person": "Helen",
        "location": "Golden Gate Park",
        "avail_start": 9 * 60 + 30,   # 9:30 AM => 570
        "avail_end": 12 * 60 + 15,      # 12:15 PM => 735
        "duration": 45
    },
    {
        "person": "Steven",
        "location": "The Castro",
        "avail_start": 20 * 60 + 15,    # 20:15 => 1215
        "avail_end": 22 * 60 + 0,       # 22:00 => 1320
        "duration": 105
    },
    {
        "person": "Deborah",
        "location": "Bayview",
        "avail_start": 8 * 60 + 30,     # 8:30 AM => 510
        "avail_end": 12 * 60 + 0,       # 12:00 PM => 720
        "duration": 30
    },
    {
        "person": "Matthew",
        "location": "Marina District",
        "avail_start": 9 * 60 + 15,     # 9:15 AM => 555
        "avail_end": 14 * 60 + 15,      # 14:15 => 855
        "duration": 45
    },
    {
        "person": "Joseph",
        "location": "Union Square",
        "avail_start": 14 * 60 + 15,    # 14:15 => 855
        "avail_end": 18 * 60 + 45,      # 18:45 => 1125
        "duration": 120
    },
    {
        "person": "Ronald",
        "location": "Sunset District",
        "avail_start": 16 * 60 + 0,     # 16:00 => 960
        "avail_end": 20 * 60 + 45,      # 20:45 => 1245
        "duration": 60
    },
    {
        "person": "Robert",
        "location": "Alamo Square",
        "avail_start": 18 * 60 + 30,    # 18:30 => 1110
        "avail_end": 21 * 60 + 15,      # 21:15 => 1275
        "duration": 120
    },
    {
        "person": "Rebecca",
        "location": "Financial District",
        "avail_start": 14 * 60 + 45,    # 14:45 => 885
        "avail_end": 16 * 60 + 15,      # 16:15 => 975
        "duration": 30
    },
    {
        "person": "Elizabeth",
        "location": "Mission District",
        "avail_start": 18 * 60 + 30,    # 18:30 => 1110
        "avail_end": 21 * 60 + 0,       # 21:00 => 1260
        "duration": 120
    }
]

# We'll use a DFS/backtracking approach to try all orders and pick the schedule with the maximum number of meetings.
def dfs(current_time, current_location, remaining_meetings, schedule):
    best_schedule = schedule[:]
    for i, meeting in enumerate(remaining_meetings):
        # Determine travel time from current_location to meeting location.
        travel = travel_times[current_location].get(meeting["location"], None)
        if travel is None:
            continue  # if no travel time defined, skip
        arrival_time = current_time + travel
        # The meeting can only start once we have arrived and the friend is available.
        start_time = max(arrival_time, meeting["avail_start"])
        end_time = start_time + meeting["duration"]
        # Check if we can finish before the friend's availability ends.
        if end_time <= meeting["avail_end"]:
            new_schedule = schedule[:] + [{
                "person": meeting["person"],
                "location": meeting["location"],
                "start": start_time,
                "end": end_time
            }]
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            candidate = dfs(end_time, meeting["location"], new_remaining, new_schedule)
            if len(candidate) > len(best_schedule):
                best_schedule = candidate
    return best_schedule

# Starting state: at Pacific Heights at 9:00 AM (540 minutes)
start_time = 9 * 60  # 540 minutes
start_location = "Pacific Heights"

# Compute the optimal schedule with maximum number of meetings.
optimal_schedule = dfs(start_time, start_location, meetings, [])

# To integrate waiting times (or gaps) our DFS solution simply finds a chain of meetings that are feasible.
# Now, we want to output the result as a JSON-formatted dictionary.
itinerary = []
for event in optimal_schedule:
    itinerary.append({
        "action": "meet",
        "location": event["location"],
        "person": event["person"],
        "start_time": minutes_to_time(event["start"]),
        "end_time": minutes_to_time(event["end"])
    })

output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))