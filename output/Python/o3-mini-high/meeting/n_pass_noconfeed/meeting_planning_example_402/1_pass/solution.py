import json
import itertools

def format_time(total_minutes):
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times (in minutes) between locations
travel_times = {
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Sunset District": 10,
        "Marina District": 16,
        "Financial District": 26,
        "Union Square": 22
    },
    "Haight-Ashbury": {
        "Golden Gate Park": 7,
        "Sunset District": 15,
        "Marina District": 17,
        "Financial District": 21,
        "Union Square": 17
    },
    "Sunset District": {
        "Golden Gate Park": 11,
        "Haight-Ashbury": 15,
        "Marina District": 21,
        "Financial District": 30,
        "Union Square": 30
    },
    "Marina District": {
        "Golden Gate Park": 18,
        "Haight-Ashbury": 16,
        "Sunset District": 19,
        "Financial District": 17,
        "Union Square": 16
    },
    "Financial District": {
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Sunset District": 31,
        "Marina District": 15,
        "Union Square": 9
    },
    "Union Square": {
        "Golden Gate Park": 22,
        "Haight-Ashbury": 18,
        "Sunset District": 26,
        "Marina District": 18,
        "Financial District": 9
    }
}

# Friends' meeting constraints.
# Times are converted to minutes from midnight.
friends = [
    {
        "person": "Sarah",
        "location": "Haight-Ashbury",
        "avail_start": 17 * 60,        # 17:00 -> 1020 minutes
        "avail_end": 21 * 60 + 30,       # 21:30 -> 1290 minutes
        "duration": 105                # minutes
    },
    {
        "person": "Patricia",
        "location": "Sunset District",
        "avail_start": 17 * 60,        # 17:00 -> 1020 minutes
        "avail_end": 19 * 60 + 45,       # 19:45 -> 1185 minutes
        "duration": 45                 # minutes
    },
    {
        "person": "Matthew",
        "location": "Marina District",
        "avail_start": 9 * 60 + 15,      # 9:15 -> 555 minutes
        "avail_end": 12 * 60,          # 12:00 -> 720 minutes
        "duration": 15                 # minutes
    },
    {
        "person": "Joseph",
        "location": "Financial District",
        "avail_start": 14 * 60 + 15,     # 14:15 -> 855 minutes
        "avail_end": 18 * 60 + 45,       # 18:45 -> 1125 minutes
        "duration": 30                 # minutes
    },
    {
        "person": "Robert",
        "location": "Union Square",
        "avail_start": 10 * 60 + 15,     # 10:15 -> 615 minutes
        "avail_end": 21 * 60 + 45,       # 21:45 -> 1305 minutes
        "duration": 15                 # minutes
    },
]

# You start at Golden Gate Park at 9:00 AM (540 minutes from midnight)
start_location = "Golden Gate Park"
start_time = 9 * 60  # 9:00 AM -> 540 minutes

best_schedule = None
best_count = 0
best_finish_time = None

# We explore all possible orders of meetings (from any subset of friends)
n = len(friends)
for r in range(1, n + 1):
    for order in itertools.permutations(friends, r):
        current_time = start_time
        current_location = start_location
        schedule = []
        feasible = True

        # Compute the schedule for this permutation
        for friend in order:
            # Determine travel time from current location to friend's location
            travel = travel_times[current_location].get(friend["location"], float('inf'))
            arrival_time = current_time + travel
            # If you arrive before friend is available, wait until their available start time
            meeting_start = max(arrival_time, friend["avail_start"])
            meeting_end = meeting_start + friend["duration"]

            # If the meeting would exceed the friend's availability window, the order fails.
            if meeting_end > friend["avail_end"]:
                feasible = False
                break

            # Add the meeting event to the schedule.
            event = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["person"],
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }
            schedule.append(event)
            # Update the current time and location to after this meeting.
            current_time = meeting_end
            current_location = friend["location"]

        # If the schedule is feasible and meets more friends (or finishes earlier in a tie), store it.
        if feasible:
            count = len(schedule)
            if count > best_count or (count == best_count and (best_finish_time is None or current_time < best_finish_time)):
                best_schedule = schedule
                best_count = count
                best_finish_time = current_time

# The output JSON with the itinerary.
result = {"itinerary": best_schedule if best_schedule is not None else []}
print(json.dumps(result, indent=2))