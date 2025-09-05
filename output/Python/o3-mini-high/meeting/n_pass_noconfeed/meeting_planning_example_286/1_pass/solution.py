import itertools
import json

# Helper functions for time conversion (to and from minutes)
def time_to_minutes(time_str):
    # time_str format: "H:MM" (24-hour)
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times (in minutes) between locations
travel_times = {
    "Union Square": {"Mission District": 14, "Bayview": 15, "Sunset District": 26},
    "Mission District": {"Union Square": 15, "Bayview": 15, "Sunset District": 24},
    "Bayview": {"Union Square": 17, "Mission District": 13, "Sunset District": 23},
    "Sunset District": {"Union Square": 30, "Mission District": 24, "Bayview": 22}
}

# Define friend meeting constraints:
# Each friend is defined by: location, available start time, available end time, and minimum meeting duration (in minutes)
friends = {
    "Carol": {
        "location": "Sunset District",
        "avail_start": time_to_minutes("10:15"),
        "avail_end": time_to_minutes("11:45"),
        "min_duration": 30
    },
    "Karen": {
        "location": "Bayview",
        "avail_start": time_to_minutes("12:45"),
        "avail_end": time_to_minutes("15:00"),
        "min_duration": 120
    },
    "Rebecca": {
        "location": "Mission District",
        "avail_start": time_to_minutes("11:30"),
        "avail_end": time_to_minutes("20:15"),
        "min_duration": 120
    }
}

# Starting conditions
start_location = "Union Square"
start_time = time_to_minutes("9:00")

# We'll try all permutations of friends and choose the itinerary that meets the constraints and maximizes the number of meetings.
best_itinerary = None
best_meeting_count = 0
best_finish_time = float("inf")

# Try all orderings of friends
for order in itertools.permutations(friends.keys()):
    current_location = start_location
    current_time = start_time
    itinerary = []
    feasible = True
    
    for friend in order:
        friend_info = friends[friend]
        destination = friend_info["location"]
        # Get travel time from current location to destination
        travel = travel_times[current_location][destination]
        arrival_time = current_time + travel
        # The meeting can start only once the friend is available.
        meeting_start = max(arrival_time, friend_info["avail_start"])
        meeting_end = meeting_start + friend_info["min_duration"]
        
        # Check if meeting ends before friend's availability ends
        if meeting_end > friend_info["avail_end"]:
            feasible = False
            break
        
        # Add meeting to itinerary for this friend
        itinerary.append({
            "action": "meet",
            "location": destination,
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update current time and location after finishing meeting
        current_time = meeting_end
        current_location = destination
        
    # Evaluate itinerary: maximize number of meetings, then minimize finish time.
    if feasible:
        meeting_count = len(itinerary)
        if meeting_count > best_meeting_count or (meeting_count == best_meeting_count and current_time < best_finish_time):
            best_meeting_count = meeting_count
            best_finish_time = current_time
            best_itinerary = itinerary

# Prepare the result as a JSON formatted dictionary
result = {"itinerary": best_itinerary if best_itinerary is not None else []}

# Output the JSON result
print(json.dumps(result))