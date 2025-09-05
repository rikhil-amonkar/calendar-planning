import json

# Helper functions to convert time string to minutes and vice versa.
def time_to_minutes(t):
    # t is expected in format "H:MM" (24-hour)
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def minutes_to_time_str(m):
    hour = m // 60
    minute = m % 60
    # Format: "H:MM" (no leading zero for hour)
    return f"{hour}:{minute:02d}"

# Travel times (in minutes) between locations.
# Note: These are directional.
travel_times = {
    "Alamo Square": {
        "Russian Hill": 13,
        "Presidio": 18,
        "Chinatown": 16,
        "Sunset District": 16,
        "The Castro": 8,
        "Embarcadero": 17,
        "Golden Gate Park": 9,
    },
    "Russian Hill": {
        "Alamo Square": 15,
        "Presidio": 14,
        "Chinatown": 9,
        "Sunset District": 23,
        "The Castro": 21,
        "Embarcadero": 8,
        "Golden Gate Park": 21,
    },
    "Presidio": {
        "Alamo Square": 18,
        "Russian Hill": 14,
        "Chinatown": 21,
        "Sunset District": 15,
        "The Castro": 21,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
    },
    "Chinatown": {
        "Alamo Square": 17,
        "Russian Hill": 7,
        "Presidio": 19,
        "Sunset District": 30,
        "The Castro": 20,
        "Embarcadero": 7,
        "Golden Gate Park": 23,
    },
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Presidio": 16,
        "Chinatown": 30,
        "The Castro": 17,
        "Embarcadero": 31,
        "Golden Gate Park": 11,
    },
    "The Castro": {
        "Alamo Square": 8,
        "Russian Hill": 18,
        "Presidio": 20,
        "Chinatown": 20,
        "Sunset District": 17,
        "Embarcadero": 22,
        "Golden Gate Park": 11,
    },
    "Embarcadero": {
        "Alamo Square": 19,
        "Russian Hill": 8,
        "Presidio": 20,
        "Chinatown": 7,
        "Sunset District": 31,
        "The Castro": 25,
        "Golden Gate Park": 25,
    },
    "Golden Gate Park": {
        "Alamo Square": 10,
        "Russian Hill": 19,
        "Presidio": 11,
        "Chinatown": 23,
        "Sunset District": 10,
        "The Castro": 13,
        "Embarcadero": 25,
    },
}

# Define friend meeting constraints.
# Each friend is defined by their name, meeting location, available time window, and minimum meeting duration (in minutes).
friends = [
    {
        "name": "Emily",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("12:15"),
        "avail_end": time_to_minutes("14:15"),
        "duration": 105,
    },
    {
        "name": "Mark",
        "location": "Presidio",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("19:30"),
        "duration": 60,
    },
    {
        "name": "Deborah",
        "location": "Chinatown",
        "avail_start": time_to_minutes("7:30"),
        "avail_end": time_to_minutes("15:30"),
        "duration": 45,
    },
    {
        "name": "Margaret",
        "location": "Sunset District",
        "avail_start": time_to_minutes("21:30"),
        "avail_end": time_to_minutes("22:30"),
        "duration": 60,
    },
    {
        "name": "George",
        "location": "The Castro",
        "avail_start": time_to_minutes("7:30"),
        "avail_end": time_to_minutes("14:15"),
        "duration": 60,
    },
    {
        "name": "Andrew",
        "location": "Embarcadero",
        "avail_start": time_to_minutes("20:15"),
        "avail_end": time_to_minutes("22:00"),
        "duration": 75,
    },
    {
        "name": "Steven",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("11:15"),
        "avail_end": time_to_minutes("21:15"),
        "duration": 105,
    },
]

# Global variables to hold the best (i.e. maximum count) schedule found.
global_best_schedule = []
global_best_count = 0

# Depth-first search to try all orders of friend meetings (non-overlapping, satisfying travel and time constraints)
def dfs(current_loc, current_time, remaining, schedule):
    global global_best_schedule, global_best_count

    # Update the best schedule if this branch has more meetings.
    if len(schedule) > global_best_count:
        global_best_count = len(schedule)
        global_best_schedule = schedule.copy()

    # Try scheduling each remaining friend next.
    for i, friend in enumerate(remaining):
        # Check if there is a direct travel time from current_loc to friend location.
        if current_loc not in travel_times or friend["location"] not in travel_times[current_loc]:
            continue  # Skip if no travel info is available.

        travel = travel_times[current_loc][friend["location"]]
        arrival_time = current_time + travel
        # We can only start the meeting when we have both arrived and the friend's availability begins.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]

        # The meeting must finish before the friend’s availability ends.
        if meeting_end <= friend["avail_end"]:
            meeting = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end),
            }
            new_schedule = schedule + [meeting]
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(friend["location"], meeting_end, new_remaining, new_schedule)

# Main function to run the scheduling search.
def main():
    start_time = time_to_minutes("9:00")
    start_location = "Alamo Square"
    dfs(start_location, start_time, friends, [])
    itinerary = {"itinerary": global_best_schedule}
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()