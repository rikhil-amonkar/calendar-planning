import json

def time_to_minutes(t):
    # t is in format "H:MM" (24-hour)
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # converts minutes (integer) to "H:MM" (24-hour, no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# All travel times between locations (in minutes) as provided.
travel_times = {
    "Russian Hill": {
        "Sunset District": 23,
        "Union Square": 10,
        "Nob Hill": 5,
        "Marina District": 7,
        "Richmond District": 14,
        "Financial District": 11,
        "Embarcadero": 8,
        "The Castro": 21,
        "Alamo Square": 15,
        "Presidio": 14
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Union Square": 30,
        "Nob Hill": 27,
        "Marina District": 21,
        "Richmond District": 12,
        "Financial District": 30,
        "Embarcadero": 30,
        "The Castro": 17,
        "Alamo Square": 17,
        "Presidio": 16
    },
    "Union Square": {
        "Russian Hill": 13,
        "Sunset District": 27,
        "Nob Hill": 9,
        "Marina District": 18,
        "Richmond District": 20,
        "Financial District": 9,
        "Embarcadero": 11,
        "The Castro": 17,
        "Alamo Square": 15,
        "Presidio": 24
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Sunset District": 24,
        "Union Square": 7,
        "Marina District": 11,
        "Richmond District": 14,
        "Financial District": 9,
        "Embarcadero": 9,
        "The Castro": 17,
        "Alamo Square": 11,
        "Presidio": 17
    },
    "Marina District": {
        "Russian Hill": 8,
        "Sunset District": 19,
        "Union Square": 16,
        "Nob Hill": 12,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 14,
        "The Castro": 22,
        "Alamo Square": 15,
        "Presidio": 10
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Sunset District": 11,
        "Union Square": 21,
        "Nob Hill": 17,
        "Marina District": 9,
        "Financial District": 22,
        "Embarcadero": 19,
        "The Castro": 16,
        "Alamo Square": 13,
        "Presidio": 7
    },
    "Financial District": {
        "Russian Hill": 11,
        "Sunset District": 30,
        "Union Square": 9,
        "Nob Hill": 8,
        "Marina District": 15,
        "Richmond District": 21,
        "Embarcadero": 4,
        "The Castro": 20,
        "Alamo Square": 17,
        "Presidio": 22
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Sunset District": 30,
        "Union Square": 10,
        "Nob Hill": 10,
        "Marina District": 12,
        "Richmond District": 21,
        "Financial District": 5,
        "The Castro": 25,
        "Alamo Square": 19,
        "Presidio": 20
    },
    "The Castro": {
        "Russian Hill": 18,
        "Sunset District": 17,
        "Union Square": 19,
        "Nob Hill": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Financial District": 21,
        "Embarcadero": 22,
        "Alamo Square": 8,
        "Presidio": 20
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Sunset District": 16,
        "Union Square": 14,
        "Nob Hill": 11,
        "Marina District": 15,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 16,
        "The Castro": 8,
        "Presidio": 17
    },
    "Presidio": {
        "Russian Hill": 14,
        "Sunset District": 15,
        "Union Square": 22,
        "Nob Hill": 18,
        "Marina District": 11,
        "Richmond District": 7,
        "Financial District": 23,
        "Embarcadero": 20,
        "The Castro": 21,
        "Alamo Square": 19
    }
}

# Meeting constraints for each friend.
meetings = [
    {   # David at Sunset District: available 9:15 to 22:00, duration 15 min.
        "person": "David",
        "location": "Sunset District",
        "avail_start": time_to_minutes("9:15"),
        "avail_end": time_to_minutes("22:00"),
        "duration": 15
    },
    {   # Kenneth at Union Square: available 21:15 to 21:45, duration 15 min.
        "person": "Kenneth",
        "location": "Union Square",
        "avail_start": time_to_minutes("21:15"),
        "avail_end": time_to_minutes("21:45"),
        "duration": 15
    },
    {   # Patricia at Nob Hill: available 15:00 to 19:15, duration 120 min.
        "person": "Patricia",
        "location": "Nob Hill",
        "avail_start": time_to_minutes("15:00"),
        "avail_end": time_to_minutes("19:15"),
        "duration": 120
    },
    {   # Mary at Marina District: available 14:45 to 16:45, duration 45 min.
        "person": "Mary",
        "location": "Marina District",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("16:45"),
        "duration": 45
    },
    {   # Charles at Richmond District: available 17:15 to 21:00, duration 15 min.
        "person": "Charles",
        "location": "Richmond District",
        "avail_start": time_to_minutes("17:15"),
        "avail_end": time_to_minutes("21:00"),
        "duration": 15
    },
    {   # Joshua at Financial District: available 14:30 to 17:15, duration 90 min.
        "person": "Joshua",
        "location": "Financial District",
        "avail_start": time_to_minutes("14:30"),
        "avail_end": time_to_minutes("17:15"),
        "duration": 90
    },
    {   # Ronald at Embarcadero: available 18:15 to 20:45, duration 30 min.
        "person": "Ronald",
        "location": "Embarcadero",
        "avail_start": time_to_minutes("18:15"),
        "avail_end": time_to_minutes("20:45"),
        "duration": 30
    },
    {   # George at The Castro: available 14:15 to 19:00, duration 105 min.
        "person": "George",
        "location": "The Castro",
        "avail_start": time_to_minutes("14:15"),
        "avail_end": time_to_minutes("19:00"),
        "duration": 105
    },
    {   # Kimberly at Alamo Square: available 9:00 to 14:30, duration 105 min.
        "person": "Kimberly",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("9:00"),
        "avail_end": time_to_minutes("14:30"),
        "duration": 105
    },
    {   # William at Presidio: available 7:00 to 12:45, duration 60 min.
        "person": "William",
        "location": "Presidio",
        "avail_start": time_to_minutes("7:00"),
        "avail_end": time_to_minutes("12:45"),
        "duration": 60
    }
]

# We'll use DFS/backtracking to find the schedule (sequence) that maximizes the number of meetings.
best_itinerary = []
best_count = 0

def dfs(current_location, current_time, remaining, itinerary):
    global best_itinerary, best_count
    # Try to schedule any remaining meeting that is feasible.
    found = False
    for i, meeting in enumerate(remaining):
        # Travel from current_location to meeting location:
        travel_time = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start at or after its availability start.
        meeting_start = max(arrival_time, meeting["avail_start"])
        finish_time = meeting_start + meeting["duration"]
        # Check if meeting can be finished before the end of availability.
        if finish_time <= meeting["avail_end"]:
            found = True
            # Append this meeting to itinerary (with computed start and finish times).
            meeting_entry = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(finish_time)
            }
            new_itinerary = itinerary + [meeting_entry]
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(meeting["location"], finish_time, new_remaining, new_itinerary)
    # If no further meeting can be scheduled from this state, update best if count is higher.
    if not found:
        if len(itinerary) > best_count:
            best_count = len(itinerary)
            best_itinerary = itinerary

# Start at Russian Hill at 9:00
start_location = "Russian Hill"
start_time = time_to_minutes("9:00")

# Run DFS search on all meetings.
dfs(start_location, start_time, meetings, [])

# Output the result as a JSON-formatted dictionary.
result = {"itinerary": best_itinerary}
print(json.dumps(result))