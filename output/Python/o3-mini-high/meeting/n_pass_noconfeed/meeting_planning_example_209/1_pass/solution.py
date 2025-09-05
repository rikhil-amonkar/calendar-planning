import json
import itertools

def time_to_minutes(t):
    # Converts "H:MM" (24-hour format) to minutes since midnight
    parts = t.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # Converts minutes since midnight to "H:MM" (24-hour format, no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) between locations
travel_times = {
    "Sunset District": {"Chinatown": 30, "Russian Hill": 24, "North Beach": 29},
    "Chinatown": {"Sunset District": 29, "Russian Hill": 7, "North Beach": 3},
    "Russian Hill": {"Sunset District": 23, "Chinatown": 9, "North Beach": 5},
    "North Beach": {"Sunset District": 27, "Chinatown": 6, "Russian Hill": 4},
}

# Define meeting constraints for each friend
meetings_info = {
    "Anthony": {
        "location": "Chinatown",
        "available_start": time_to_minutes("13:15"),
        "available_end": time_to_minutes("14:30"),
        "duration": 60
    },
    "Rebecca": {
        "location": "Russian Hill",
        "available_start": time_to_minutes("19:30"),
        "available_end": time_to_minutes("21:15"),
        "duration": 105
    },
    "Melissa": {
        "location": "North Beach",
        "available_start": time_to_minutes("8:15"),
        "available_end": time_to_minutes("13:30"),
        "duration": 105
    }
}

# Starting conditions: you arrive at Sunset District at 9:00AM
start_location = "Sunset District"
start_time = time_to_minutes("9:00")

# We want to meet as many friends as possible.
# Try all permutations (for 3, then 2, then 1 meetings) and pick the schedule with the most meetings that satisfies all constraints.
best_itinerary = None
best_count = 0
persons = list(meetings_info.keys())

# Check permutations from the largest possible group size down to 1
for r in range(len(persons), 0, -1):
    for perm in itertools.permutations(persons, r):
        itinerary = []
        current_time = start_time
        current_location = start_location
        valid = True
        # Build the itinerary for this permutation
        for person in perm:
            meeting = meetings_info[person]
            meeting_location = meeting["location"]
            # Compute travel time from current location to the meeting location
            travel = travel_times[current_location][meeting_location]
            arrival_time = current_time + travel
            # Meeting cannot start before the person's available start time
            meeting_start = max(arrival_time, meeting["available_start"])
            meeting_end = meeting_start + meeting["duration"]
            # If meeting cannot be completed within the available window, discard this permutation
            if meeting_end > meeting["available_end"]:
                valid = False
                break
            itinerary.append({
                "action": "meet",
                "location": meeting_location,
                "person": person,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = meeting_location
        if valid and len(perm) > best_count:
            best_itinerary = itinerary
            best_count = len(perm)
    if best_itinerary is not None:
        # Found the optimal itinerary with the maximum number of meetings
        break

result = {"itinerary": best_itinerary if best_itinerary is not None else []}
print(json.dumps(result, indent=2))