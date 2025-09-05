import json

# Utility functions to convert time between "H:MM" string format and minutes since midnight.
def time_to_minutes(t):
    hours, minutes = t.split(":")
    return int(hours) * 60 + int(minutes)

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Define the travel times (in minutes) between locations.
travel_times = {
    "The Castro": {
        "Marina District": 21,
        "Presidio": 20,
        "North Beach": 20,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Sunset District": 17
    },
    "Marina District": {
        "The Castro": 22,
        "Presidio": 10,
        "North Beach": 11,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Golden Gate Park": 18,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Sunset District": 19
    },
    "Presidio": {
        "The Castro": 21,
        "Marina District": 11,
        "North Beach": 18,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 12,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Sunset District": 15
    },
    "North Beach": {
        "The Castro": 23,
        "Marina District": 9,
        "Presidio": 17,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Golden Gate Park": 22,
        "Richmond District": 18,
        "Alamo Square": 16,
        "Financial District": 8,
        "Sunset District": 27
    },
    "Embarcadero": {
        "The Castro": 25,
        "Marina District": 12,
        "Presidio": 20,
        "North Beach": 5,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Richmond District": 21,
        "Alamo Square": 19,
        "Financial District": 5,
        "Sunset District": 30
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Marina District": 17,
        "Presidio": 15,
        "North Beach": 19,
        "Embarcadero": 20,
        "Golden Gate Park": 7,
        "Richmond District": 10,
        "Alamo Square": 5,
        "Financial District": 21,
        "Sunset District": 15
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Marina District": 16,
        "Presidio": 11,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Alamo Square": 9,
        "Financial District": 26,
        "Sunset District": 10
    },
    "Richmond District": {
        "The Castro": 16,
        "Marina District": 9,
        "Presidio": 7,
        "North Beach": 17,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Golden Gate Park": 9,
        "Alamo Square": 13,
        "Financial District": 22,
        "Sunset District": 11
    },
    "Alamo Square": {
        "The Castro": 8,
        "Marina District": 15,
        "Presidio": 17,
        "North Beach": 15,
        "Embarcadero": 16,
        "Haight-Ashbury": 5,
        "Golden Gate Park": 9,
        "Richmond District": 11,
        "Financial District": 17,
        "Sunset District": 16
    },
    "Financial District": {
        "The Castro": 20,
        "Marina District": 15,
        "Presidio": 22,
        "North Beach": 7,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Sunset District": 30
    },
    "Sunset District": {
        "The Castro": 17,
        "Marina District": 21,
        "Presidio": 16,
        "North Beach": 28,
        "Embarcadero": 30,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Richmond District": 12,
        "Alamo Square": 17,
        "Financial District": 30
    }
}

# Define the meeting constraints and parameters.
# Each meeting candidate has: person, location, availability window, and minimum meeting duration (in minutes).
meetings = [
    {
        "person": "Joshua",
        "location": "Presidio",
        "avail_start": time_to_minutes("8:30"),
        "avail_end": time_to_minutes("13:15"),
        "duration": 105
    },
    {
        "person": "David",
        "location": "Embarcadero",
        "avail_start": time_to_minutes("10:45"),
        "avail_end": time_to_minutes("12:30"),
        "duration": 30
    },
    {
        "person": "Stephanie",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("15:30"),
        "avail_end": time_to_minutes("16:30"),
        "duration": 30
    },
    {
        "person": "Helen",
        "location": "Financial District",
        "avail_start": time_to_minutes("17:30"),
        "avail_end": time_to_minutes("18:30"),
        "duration": 45
    },
    {
        "person": "Kimberly",
        "location": "Haight-Ashbury",
        "avail_start": time_to_minutes("16:45"),
        "avail_end": time_to_minutes("21:30"),
        "duration": 75
    },
    {
        "person": "Lisa",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("17:30"),
        "avail_end": time_to_minutes("21:45"),
        "duration": 45
    },
    {
        "person": "Ronald",
        "location": "Richmond District",
        "avail_start": time_to_minutes("8:00"),
        "avail_end": time_to_minutes("9:30"),
        "duration": 90
    },
    {
        "person": "Elizabeth",
        "location": "Marina District",
        "avail_start": time_to_minutes("19:00"),
        "avail_end": time_to_minutes("20:45"),
        "duration": 105
    },
    {
        "person": "Laura",
        "location": "Sunset District",
        "avail_start": time_to_minutes("17:45"),
        "avail_end": time_to_minutes("21:15"),
        "duration": 90
    },
    {
        "person": "Timothy",
        "location": "North Beach",
        "avail_start": time_to_minutes("19:45"),
        "avail_end": time_to_minutes("22:00"),
        "duration": 90
    }
]

# Use a depth-first search (DFS) to explore feasible meeting orders and pick the one with the maximum number of meetings.
def dfs(current_location, current_time, remaining_meetings, current_schedule):
    best_schedule = current_schedule[:]
    best_count = len(current_schedule)
    
    for meeting in remaining_meetings:
        # Check if travel time is available from current_location to the meeting's location.
        if current_location not in travel_times or meeting["location"] not in travel_times[current_location]:
            continue
        travel = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel
        # The meeting can start only when both you have arrived and the friend is available.
        start_time = max(arrival_time, meeting["avail_start"])
        finish_time = start_time + meeting["duration"]
        # Check if the meeting can be completed within the friend's availability window.
        if finish_time <= meeting["avail_end"]:
            new_schedule = current_schedule + [{
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(finish_time)
            }]
            new_remaining = [m for m in remaining_meetings if m != meeting]
            rec_schedule = dfs(meeting["location"], finish_time, new_remaining, new_schedule)
            if len(rec_schedule) > best_count:
                best_schedule = rec_schedule
                best_count = len(rec_schedule)
    return best_schedule

# Starting point: Arrive at "The Castro" at 9:00.
start_location = "The Castro"
start_time = time_to_minutes("9:00")

# Compute the optimal meeting itinerary.
optimal_itinerary = dfs(start_location, start_time, meetings, [])

# Prepare the output in the required JSON format.
output = {"itinerary": optimal_itinerary}
print(json.dumps(output, indent=2))