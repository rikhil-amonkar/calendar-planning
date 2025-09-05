import datetime
import json

# Helper functions to parse and format times.
def parse_time(time_str):
    # Expects time string in "H:MM" format; returns a datetime object on an arbitrary day.
    parts = time_str.split(":")
    return datetime.datetime(2000, 1, 1, int(parts[0]), int(parts[1]))

def format_time(dt):
    # Format time as "H:MM" without a leading zero for the hour.
    return f"{dt.hour}:{dt.minute:02d}"

# Travel times in minutes between locations.
travel_times = {
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Bayview"): 23,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 26,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22
}

# Define the meeting constraints for each friend.
friends = [
    {
        "name": "Matthew",
        "location": "Presidio",
        "start": parse_time("11:00"),
        "end": parse_time("21:00"),
        "duration": 90  # minutes
    },
    {
        "name": "Margaret",
        "location": "Chinatown",
        "start": parse_time("9:15"),
        "end": parse_time("18:45"),
        "duration": 90
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "start": parse_time("14:15"),
        "end": parse_time("17:00"),
        "duration": 15
    },
    {
        "name": "Helen",
        "location": "Richmond District",
        "start": parse_time("19:45"),
        "end": parse_time("22:00"),
        "duration": 60
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "start": parse_time("21:15"),
        "end": parse_time("22:15"),
        "duration": 60
    },
    {
        "name": "Kimberly",
        "location": "Golden Gate Park",
        "start": parse_time("13:00"),
        "end": parse_time("16:30"),
        "duration": 120
    },
    {
        "name": "Kenneth",
        "location": "Bayview",
        "start": parse_time("14:30"),
        "end": parse_time("18:00"),
        "duration": 60
    }
]

# Global variables to track the best schedule found.
best_schedule = []
best_count = 0

def backtrack(current_time, current_loc, remaining, current_schedule):
    global best_schedule, best_count
    # Update best schedule if current one has more meetings.
    if len(current_schedule) > best_count:
        best_schedule = current_schedule.copy()
        best_count = len(current_schedule)
    # Try scheduling each of the remaining friends.
    for i, friend in enumerate(remaining):
        # Get travel time from current location to the friend's location.
        key = (current_loc, friend["location"])
        if key not in travel_times:
            continue  # Skip if no travel time is defined
        travel = travel_times[key]
        arrival = current_time + datetime.timedelta(minutes=travel)
        # The meeting can only start when both you have arrived and the friend is available.
        meet_start = arrival if arrival > friend["start"] else friend["start"]
        meet_end = meet_start + datetime.timedelta(minutes=friend["duration"])
        # Check if the meeting can be held within the friend's available window.
        if meet_end <= friend["end"]:
            entry = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": format_time(meet_start),
                "end_time": format_time(meet_end)
            }
            new_schedule = current_schedule + [entry]
            new_remaining = remaining[:i] + remaining[i+1:]
            backtrack(meet_end, friend["location"], new_remaining, new_schedule)

def main():
    # Starting point: Arrive at Russian Hill at 9:00.
    start_loc = "Russian Hill"
    start_time = parse_time("9:00")
    # Begin backtracking search for the optimal schedule (maximizing number of meetings).
    backtrack(start_time, start_loc, friends, [])
    
    # Prepare the final JSON result.
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()