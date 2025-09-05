import json

def time_to_minutes(t):
    # expects format "H:MM" or "HH:MM"
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel distances in minutes (from, to) based on provided data
travel_distances = {
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Pacific Heights"): 23,

    ("North Beach", "Bayview"): 25,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Pacific Heights"): 8,

    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,

    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,

    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Pacific Heights"): 8,

    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,

    ("Union Square", "Bayview"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,

    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Pacific Heights"): 10,

    ("Presidio", "Bayview"): 31,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Pacific Heights"): 11,

    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,

    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
}

# Appointment details for each friend (availability window and required meeting duration in minutes)
appointments = [
    {
        "person": "Brian",
        "location": "North Beach",
        "window_start": time_to_minutes("13:00"),
        "window_end": time_to_minutes("19:00"),
        "duration": 90
    },
    {
        "person": "Richard",
        "location": "Fisherman's Wharf",
        "window_start": time_to_minutes("11:00"),
        "window_end": time_to_minutes("12:45"),
        "duration": 60
    },
    {
        "person": "Ashley",
        "location": "Haight-Ashbury",
        "window_start": time_to_minutes("15:00"),
        "window_end": time_to_minutes("20:30"),
        "duration": 90
    },
    {
        "person": "Elizabeth",
        "location": "Nob Hill",
        "window_start": time_to_minutes("11:45"),
        "window_end": time_to_minutes("18:30"),
        "duration": 75
    },
    {
        "person": "Jessica",
        "location": "Golden Gate Park",
        "window_start": time_to_minutes("20:00"),
        "window_end": time_to_minutes("21:45"),
        "duration": 105
    },
    {
        "person": "Deborah",
        "location": "Union Square",
        "window_start": time_to_minutes("17:30"),
        "window_end": time_to_minutes("22:00"),
        "duration": 60
    },
    {
        "person": "Kimberly",
        "location": "Alamo Square",
        "window_start": time_to_minutes("17:30"),
        "window_end": time_to_minutes("21:15"),
        "duration": 45
    },
    {
        "person": "Matthew",
        "location": "Presidio",
        "window_start": time_to_minutes("8:15"),
        "window_end": time_to_minutes("9:00"),
        "duration": 15
    },
    {
        "person": "Kenneth",
        "location": "Chinatown",
        "window_start": time_to_minutes("13:45"),
        "window_end": time_to_minutes("19:30"),
        "duration": 105
    },
    {
        "person": "Anthony",
        "location": "Pacific Heights",
        "window_start": time_to_minutes("14:15"),
        "window_end": time_to_minutes("16:00"),
        "duration": 30
    }
]

# Global variables to track the best schedule (maximizing number of meetings)
best_schedule = []
max_meetings = 0

def dfs(current_time, current_location, visited, schedule):
    global best_schedule, max_meetings
    found_next = False
    for i, app in enumerate(appointments):
        if i in visited:
            continue
        # Check travel time from current location to appointment location.
        if (current_location, app["location"]) not in travel_distances:
            continue
        travel_time = travel_distances[(current_location, app["location"])]
        arrival_time = current_time + travel_time
        # The meeting can begin no earlier than the friend's available window start time.
        meeting_start = max(arrival_time, app["window_start"])
        meeting_end = meeting_start + app["duration"]
        if meeting_end <= app["window_end"]:
            found_next = True
            visited.add(i)
            new_schedule = schedule + [{
                "action": "meet",
                "location": app["location"],
                "person": app["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }]
            dfs(meeting_end, app["location"], visited, new_schedule)
            visited.remove(i)
    if not found_next:
        if len(schedule) > max_meetings:
            max_meetings = len(schedule)
            best_schedule = schedule

def main():
    # You arrive at Bayview at 9:00 AM
    start_time = time_to_minutes("9:00")
    start_location = "Bayview"
    visited = set()
    dfs(start_time, start_location, visited, [])
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()