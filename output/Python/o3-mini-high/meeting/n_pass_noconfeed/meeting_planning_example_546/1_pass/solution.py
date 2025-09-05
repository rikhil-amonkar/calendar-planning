import itertools
import json

# Define travel times (in minutes) between locations.
travel_times = {
    "Embarcadero": {
        "Richmond District": 21,
        "Union Square": 10,
        "Financial District": 5,
        "Pacific Heights": 11,
        "Nob Hill": 10,
        "Bayview": 21
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Union Square": 21,
        "Financial District": 22,
        "Pacific Heights": 10,
        "Nob Hill": 17,
        "Bayview": 26
    },
    "Union Square": {
        "Embarcadero": 11,
        "Richmond District": 20,
        "Financial District": 9,
        "Pacific Heights": 15,
        "Nob Hill": 9,
        "Bayview": 15
    },
    "Financial District": {
        "Embarcadero": 4,
        "Richmond District": 21,
        "Union Square": 9,
        "Pacific Heights": 13,
        "Nob Hill": 8,
        "Bayview": 19
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Richmond District": 12,
        "Union Square": 12,
        "Financial District": 13,
        "Nob Hill": 8,
        "Bayview": 22
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Richmond District": 14,
        "Union Square": 7,
        "Financial District": 9,
        "Pacific Heights": 8,
        "Bayview": 19
    },
    "Bayview": {
        "Embarcadero": 19,
        "Richmond District": 25,
        "Union Square": 17,
        "Financial District": 19,
        "Pacific Heights": 23,
        "Nob Hill": 20
    }
}

# Define meeting constraints for each friend.
# Times are in minutes from midnight.
# For example, 9:00AM = 9*60 = 540, 16:30 = 16*60+30 = 990, 21:15 = 21*60+15 = 1275, etc.
people = [
    {
        "name": "Kenneth",
        "location": "Richmond District",
        "start": 1275,  # 21:15
        "end": 1320,    # 22:00
        "duration": 30
    },
    {
        "name": "Lisa",
        "location": "Union Square",
        "start": 540,   # 9:00
        "end": 990,     # 16:30
        "duration": 45
    },
    {
        "name": "Joshua",
        "location": "Financial District",
        "start": 720,   # 12:00
        "end": 915,     # 15:15
        "duration": 15
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "start": 480,   # 8:00
        "end": 690,     # 11:30
        "duration": 90
    },
    {
        "name": "Andrew",
        "location": "Nob Hill",
        "start": 690,   # 11:30
        "end": 1215,    # 20:15
        "duration": 60
    },
    {
        "name": "John",
        "location": "Bayview",
        "start": 1005,  # 16:45
        "end": 1290,    # 21:30
        "duration": 75
    }
]

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Simulation function tries to schedule meetings sequentially in a given order,
# starting from Embarcadero at 9:00 (540 minutes).
# It returns the scheduled meetings and the final finish time.
def simulate_schedule(order, travel_times, start_time=540, start_location="Embarcadero"):
    current_time = start_time
    current_location = start_location
    schedule = []
    for friend in order:
        # Check travel time from current location to friend's meeting location.
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            return None, None
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # Meeting can only start when the friend is available.
        meeting_start = max(arrival_time, friend["start"])
        meeting_end = meeting_start + friend["duration"]
        # If meeting cannot be completed within the friend's available window, fail this order.
        if meeting_end > friend["end"]:
            return None, None
        schedule.append({
            "person": friend["name"],
            "location": friend["location"],
            "start": meeting_start,
            "end": meeting_end
        })
        current_time = meeting_end
        current_location = friend["location"]
    return schedule, current_time

# To account for the possibility of partial schedules (meeting as many friends as possible)
# we simulate the schedule step-by-step and count how many meetings get scheduled.
def simulate_partial_schedule(order, travel_times, start_time=540, start_location="Embarcadero"):
    current_time = start_time
    current_location = start_location
    scheduled = []
    for friend in order:
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            break
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        meeting_start = max(arrival_time, friend["start"])
        meeting_end = meeting_start + friend["duration"]
        if meeting_end > friend["end"]:
            break
        scheduled.append({
            "person": friend["name"],
            "location": friend["location"],
            "start": meeting_start,
            "end": meeting_end
        })
        current_time = meeting_end
        current_location = friend["location"]
    return scheduled, current_time

# Search over all permutations to find the schedule that meets the maximum number of friends.
# If more than one schedule has the same number, choose the one with the earliest finish time.
best_schedule = None
best_count = 0
best_finish = float('inf')

for perm in itertools.permutations(people):
    sch, finish_time = simulate_partial_schedule(perm, travel_times)
    if sch is None:
        continue
    count = len(sch)
    if count > best_count or (count == best_count and finish_time < best_finish):
        best_schedule = sch
        best_count = count
        best_finish = finish_time
    # Early exit if we found a full schedule meeting all six friends.
    if best_count == len(people):
        # Continue searching to see if any schedule finishes even earlier.
        continue

# Prepare the itinerary in the desired JSON format.
itinerary = []
if best_schedule:
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time_str(meeting["start"]),
            "end_time": minutes_to_time_str(meeting["end"])
        })

output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))