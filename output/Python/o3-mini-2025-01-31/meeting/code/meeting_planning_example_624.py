#!/usr/bin/env python3
import json
import itertools

# Helper: convert HH:MM to minutes since midnight
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

# Helper: convert minutes since midnight to H:MM (24-hour format, no leading zero for hour)
def minutes_to_time(m):
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

# Travel times in minutes (directly from the provided data)
# We'll structure the data as a dictionary of dictionaries.
travel_times = {
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Chinatown": 23,
        "Alamo Square": 10,
        "North Beach": 24,
        "Russian Hill": 19
    },
    "Haight-Ashbury": {
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "The Castro": 6,
        "Chinatown": 19,
        "Alamo Square": 5,
        "North Beach": 19,
        "Russian Hill": 17
    },
    "Fisherman's Wharf": {
        "Golden Gate Park": 25,
        "Haight-Ashbury": 22,
        "The Castro": 26,
        "Chinatown": 12,
        "Alamo Square": 20,
        "North Beach": 6,
        "Russian Hill": 7
    },
    "The Castro": {
        "Golden Gate Park": 11,
        "Haight-Ashbury": 6,
        "Fisherman's Wharf": 24,
        "Chinatown": 20,
        "Alamo Square": 8,
        "North Beach": 20,
        "Russian Hill": 18
    },
    "Chinatown": {
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 8,
        "The Castro": 22,
        "Alamo Square": 17,
        "North Beach": 3,
        "Russian Hill": 7
    },
    "Alamo Square": {
        "Golden Gate Park": 9,
        "Haight-Ashbury": 5,
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Chinatown": 16,
        "North Beach": 15,
        "Russian Hill": 13
    },
    "North Beach": {
        "Golden Gate Park": 22,
        "Haight-Ashbury": 18,
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Chinatown": 6,
        "Alamo Square": 16,
        "Russian Hill": 4
    },
    "Russian Hill": {
        "Golden Gate Park": 21,
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Chinatown": 9,
        "Alamo Square": 15,
        "North Beach": 5
    }
}

# Friend meeting constraints.
# Each friend is represented as a dictionary with:
# "person", "location", "avail_start", "avail_end", "duration" (in minutes)
friends = [
    {
        "person": "Carol",
        "location": "Haight-Ashbury",
        "avail_start": time_to_minutes("21:30"),
        "avail_end": time_to_minutes("22:30"),
        "duration": 60
    },
    {
        "person": "Laura",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("11:45"),
        "avail_end": time_to_minutes("21:30"),
        "duration": 60
    },
    {
        "person": "Karen",
        "location": "The Castro",
        "avail_start": time_to_minutes("7:15"),
        "avail_end": time_to_minutes("14:00"),
        "duration": 75
    },
    {
        "person": "Elizabeth",
        "location": "Chinatown",
        "avail_start": time_to_minutes("12:15"),
        "avail_end": time_to_minutes("21:30"),
        "duration": 75
    },
    {
        "person": "Deborah",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("12:00"),
        "avail_end": time_to_minutes("15:00"),
        "duration": 105
    },
    {
        "person": "Jason",
        "location": "North Beach",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("19:00"),
        "duration": 90
    },
    {
        "person": "Steven",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("18:30"),
        "duration": 120
    }
]

# Starting point and start time
start_location = "Golden Gate Park"
start_time = time_to_minutes("9:00")

# Function to retrieve travel time between two locations
def get_travel_time(frm, to):
    if frm == to:
        return 0
    # if key not directly available, try swapping if symmetric
    if frm in travel_times and to in travel_times[frm]:
        return travel_times[frm][to]
    elif to in travel_times and frm in travel_times[to]:
        return travel_times[to][frm]
    else:
        # if not found, assume a large travel time
        return 999

# Given an ordering of friend meetings, simulate the schedule.
# Returns (feasible, itinerary, final_end_time) if schedule is possible, else (False, None, None)
def simulate_schedule(order):
    itinerary = []
    current_location = start_location
    current_time = start_time

    for friend in order:
        # Travel to friend's location
        travel = get_travel_time(current_location, friend["location"])
        arrival_time = current_time + travel
        # Wait if arrived before friend's available start
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting can finish before friend's available end
        if meeting_end > friend["avail_end"]:
            return (False, None, None)
        # Append the meeting event to itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        # Update current time and location
        current_time = meeting_end
        current_location = friend["location"]
    return (True, itinerary, current_time)

# We want to schedule as many meetings as possible.
# Here, we search over all permutations and choose the one that meets the largest number of meetings.
# In our case, we try to schedule all 7 meetings if possible.
best_itinerary = None
best_count = 0
best_end_time = None

# Loop over all permutations of the 7 friends.
for perm in itertools.permutations(friends):
    feasible, itinerary, final_end_time = simulate_schedule(perm)
    if feasible:
        count = len(itinerary)
        if count > best_count:
            best_count = count
            best_itinerary = itinerary
            best_end_time = final_end_time
        elif count == best_count:
            # tie-breaker: choose the one finishing earlier (optimizing overall schedule length)
            if best_end_time is None or final_end_time < best_end_time:
                best_itinerary = itinerary
                best_end_time = final_end_time

# If a feasible itinerary that covers all meetings was not found, try partial meetings.
if best_itinerary is None:
    # We try subsets in descending order of meeting count.
    for count in range(len(friends), 0, -1):
        for subset in itertools.combinations(friends, count):
            for perm in itertools.permutations(subset):
                feasible, itinerary, final_end_time = simulate_schedule(perm)
                if feasible:
                    best_itinerary = itinerary
                    best_count = len(itinerary)
                    best_end_time = final_end_time
                    break
            if best_itinerary is not None:
                break
        if best_itinerary is not None:
            break

# Output the best itinerary in the required JSON format
output = {
    "itinerary": best_itinerary if best_itinerary is not None else []
}

print(json.dumps(output, indent=2))
                    
if __name__ == "__main__":
    pass