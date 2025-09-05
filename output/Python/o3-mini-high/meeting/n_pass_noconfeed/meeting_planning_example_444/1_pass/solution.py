import json

# Travel times in minutes between locations
travel_times = {
    "Financial District": {
        "Russian Hill": 10,
        "Sunset District": 31,
        "North Beach": 7,
        "The Castro": 23,
        "Golden Gate Park": 23,
    },
    "Russian Hill": {
        "Financial District": 11,
        "Sunset District": 23,
        "North Beach": 5,
        "The Castro": 21,
        "Golden Gate Park": 21,
    },
    "Sunset District": {
        "Financial District": 30,
        "Russian Hill": 24,
        "North Beach": 29,
        "The Castro": 17,
        "Golden Gate Park": 11,
    },
    "North Beach": {
        "Financial District": 8,
        "Russian Hill": 4,
        "Sunset District": 27,
        "The Castro": 22,
        "Golden Gate Park": 22,
    },
    "The Castro": {
        "Financial District": 20,
        "Russian Hill": 18,
        "Sunset District": 17,
        "North Beach": 20,
        "Golden Gate Park": 11,
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Russian Hill": 19,
        "Sunset District": 10,
        "North Beach": 24,
        "The Castro": 13,
    },
}

# Friend meeting constraints.
# Times are in minutes since midnight.
# 9:00 AM = 540 minutes.
# For each friend, we have: name, location, available start, available end, and minimum meeting duration.
friends = [
    {
        "name": "Ronald",
        "location": "Russian Hill",
        "start": 13 * 60 + 45,  # 13:45 = 825 minutes
        "end": 17 * 60 + 15,    # 17:15 = 1035 minutes
        "duration": 105
    },
    {
        "name": "Patricia",
        "location": "Sunset District",
        "start": 9 * 60 + 15,   # 9:15 = 555 minutes
        "end": 22 * 60,         # 22:00 = 1320 minutes
        "duration": 60
    },
    {
        "name": "Laura",
        "location": "North Beach",
        "start": 12 * 60 + 30,  # 12:30 = 750 minutes
        "end": 12 * 60 + 45,    # 12:45 = 765 minutes
        "duration": 15
    },
    {
        "name": "Emily",
        "location": "The Castro",
        "start": 16 * 60 + 15,  # 16:15 = 975 minutes
        "end": 18 * 60 + 30,    # 18:30 = 1110 minutes
        "duration": 60
    },
    {
        "name": "Mary",
        "location": "Golden Gate Park",
        "start": 15 * 60,       # 15:00 = 900 minutes
        "end": 16 * 60 + 30,    # 16:30 = 990 minutes
        "duration": 60
    },
]

def format_time(minutes):
    """ Convert minutes since midnight to 'H:MM' time format using 24-hour clock. """
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Global variables to track the best itinerary (one that maximizes number of meetings)
best_itinerary = []
max_meetings = 0

def dfs(current_time, current_location, remaining, itinerary):
    global best_itinerary, max_meetings
    # Update the best itinerary if this one has more meetings.
    if len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary[:]
    # Try scheduling each remaining meeting next.
    for i, friend in enumerate(remaining):
        # Calculate travel time from current location to friend's location (0 if already there)
        travel = 0 if current_location == friend["location"] else travel_times[current_location][friend["location"]]
        arrival = current_time + travel
        meeting_start = max(arrival, friend["start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if the meeting can be scheduled within the friend's availability window.
        if meeting_end <= friend["end"]:
            meeting = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            }
            # Recurse with updated time, location, and remaining friend list.
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(meeting_end, friend["location"], new_remaining, itinerary + [meeting])

# Start the day at the Financial District at 9:00 AM (540 minutes)
start_time = 9 * 60
dfs(start_time, "Financial District", friends, [])

# Build the result dictionary in the required JSON format.
result = {
    "itinerary": best_itinerary
}

# Output the result as JSON.
print(json.dumps(result, indent=2))