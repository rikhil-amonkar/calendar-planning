import json
from itertools import permutations

# Helper functions
def minutes(h, m):
    return h * 60 + m

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables (constraints and travel times)
locations = ["Pacific Heights", "Presidio", "Marina District"]
start_location = "Pacific Heights"
arrival_time = minutes(9, 0)

travel = {
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Marina District"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Presidio"): 10,
}

people = {
    "Jason": {
        "location": "Presidio",
        "start": minutes(10, 0),
        "end": minutes(16, 15),
        "min_duration": 90
    },
    "Kenneth": {
        "location": "Marina District",
        "start": minutes(15, 30),
        "end": minutes(16, 45),
        "min_duration": 45
    }
}

# Scheduling logic
def schedule_order(order_names):
    current_loc = start_location
    current_time = arrival_time
    itinerary = []
    total_meeting_time = 0

    order = [people[name] | {"name": name} for name in order_names]

    for i, person in enumerate(order):
        # Travel to person's location
        t = travel.get((current_loc, person["location"]))
        if t is None:
            return None  # No travel path
        arrival = current_time + t

        start_time = max(arrival, person["start"])
        # Check feasibility for minimum duration
        if start_time > person["end"] - person["min_duration"]:
            return None

        if i < len(order) - 1:
            nextp = order[i + 1]
            t_next = travel.get((person["location"], nextp["location"]))
            if t_next is None:
                return None

            # Latest we can end current meeting while ensuring next person's minimum can be met
            latest_end_allowing_next = nextp["end"] - nextp["min_duration"] - t_next
            end_time = min(person["end"], latest_end_allowing_next)
            if end_time < start_time + person["min_duration"]:
                return None
        else:
            # Last person: meet until their availability end to maximize total meeting time
            end_time = person["end"]
            if end_time - start_time < person["min_duration"]:
                return None

        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": fmt_time(start_time),
            "end_time": fmt_time(end_time)
        })
        total_meeting_time += end_time - start_time
        current_time = end_time
        current_loc = person["location"]

    return {
        "itinerary": itinerary,
        "friends_met": len(order),
        "total_meeting_time": total_meeting_time,
        "end_time": current_time
    }

def schedule_single(name):
    person = people[name] | {"name": name}
    current_loc = start_location
    current_time = arrival_time

    t = travel.get((current_loc, person["location"]))
    if t is None:
        return None
    arrival = current_time + t
    start_time = max(arrival, person["start"])
    end_time = person["end"]

    if end_time - start_time < person["min_duration"]:
        return None

    itinerary = [{
        "action": "meet",
        "location": person["location"],
        "person": person["name"],
        "start_time": fmt_time(start_time),
        "end_time": fmt_time(end_time)
    }]

    return {
        "itinerary": itinerary,
        "friends_met": 1,
        "total_meeting_time": end_time - start_time,
        "end_time": end_time
    }

# Generate candidates (all permutations and singles)
candidates = []

for order in permutations(people.keys(), 2):
    s = schedule_order(order)
    if s:
        candidates.append(s)

for name in people.keys():
    s = schedule_single(name)
    if s:
        candidates.append(s)

# Choose the optimal schedule
def score(sol):
    # Primary: maximize number of friends met
    # Secondary: maximize total meeting time
    # Tertiary: minimize end time (earlier finish)
    return (sol["friends_met"], sol["total_meeting_time"], -sol["end_time"])

best = max(candidates, key=score) if candidates else {"itinerary": []}

# Output JSON
print(json.dumps({"itinerary": best["itinerary"]}, ensure_ascii=False))