import json
import itertools

def to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) between locations
travel_times = {
    "Sunset District": {"North Beach": 29, "Union Square": 30, "Alamo Square": 17},
    "North Beach": {"Sunset District": 27, "Union Square": 7, "Alamo Square": 16},
    "Union Square": {"Sunset District": 26, "North Beach": 10, "Alamo Square": 15},
    "Alamo Square": {"Sunset District": 16, "North Beach": 15, "Union Square": 14},
}

# Meeting constraints (times in minutes from midnight)
# 9:00 AM = 540 minutes
start_location = "Sunset District"
start_time = 540  # 9:00 AM

# Friends meeting details:
# Sarah: location North Beach, available 16:00 (960) to 18:15 (1095), minimum 60 minutes.
# Jeffrey: location Union Square, available 15:00 (900) to 22:00 (1320), minimum 75 minutes.
# Brian: location Alamo Square, available 16:00 (960) to 17:30 (1050), minimum 75 minutes.
meetings = [
    {
        "person": "Sarah",
        "location": "North Beach",
        "avail_start": 960,   # 16:00
        "avail_end": 1095,    # 18:15
        "duration": 60
    },
    {
        "person": "Jeffrey",
        "location": "Union Square",
        "avail_start": 900,   # 15:00
        "avail_end": 1320,    # 22:00
        "duration": 75
    },
    {
        "person": "Brian",
        "location": "Alamo Square",
        "avail_start": 960,   # 16:00
        "avail_end": 1050,    # 17:30
        "duration": 75
    }
]

# We'll try all possible orders (subsets and permutations) of meetings
candidates = []

# Consider subsets of meetings of various sizes
for r in range(1, len(meetings) + 1):
    for perm in itertools.permutations(meetings, r):
        current_time = start_time
        current_location = start_location
        itinerary = []
        feasible = True
        # Process each meeting in the permutation order
        for meeting in perm:
            # Compute travel time from current_location to the meeting location
            travel_time = travel_times[current_location][meeting["location"]]
            arrival_time = current_time + travel_time
            # The meeting can only start when the friend is available.
            meeting_start = max(arrival_time, meeting["avail_start"])
            meeting_end = meeting_start + meeting["duration"]
            # Check if the meeting can be completed within the available window.
            if meeting_end > meeting["avail_end"]:
                feasible = False
                break
            # Record this meeting in the itinerary
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": to_time_str(meeting_start),
                "end_time": to_time_str(meeting_end)
            })
            # Update current state for the next leg of the journey
            current_time = meeting_end
            current_location = meeting["location"]
        if feasible:
            candidates.append({
                "itinerary": itinerary,
                "count": len(perm),
                "finish_time": current_time
            })

# Select the schedule that meets the maximum number of friends.
# In case of a tie, choose the one that finishes earliest.
if candidates:
    best = sorted(candidates, key=lambda x: (-x["count"], x["finish_time"]))[0]
else:
    best = {"itinerary": []}

result = {"itinerary": best["itinerary"]}
print(json.dumps(result, indent=2))