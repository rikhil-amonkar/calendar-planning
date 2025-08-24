"SOLUTION:"

import json
from itertools import permutations

def parse_time(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (meeting constraints and travel times)
start_location = "Embarcadero"
arrival_time_str = "9:00"

travel_times = {
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Alamo Square"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Alamo Square"): 17,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Financial District"): 17,
}

people = {
    "Stephanie": {
        "location": "Financial District",
        "start": "8:15",
        "end": "11:30",
        "min_meet": 90,
    },
    "John": {
        "location": "Alamo Square",
        "start": "10:15",
        "end": "20:45",
        "min_meet": 30,
    },
}

# Convert input times to minutes
arrival_time = parse_time(arrival_time_str)
for p in people.values():
    p["start_min"] = parse_time(p["start"])
    p["end_min"] = parse_time(p["end"])

def compute_two_order(order):
    # Returns best itinerary for given order, or None if infeasible
    p1_name, p2_name = order
    p1 = people[p1_name]
    p2 = people[p2_name]

    # Travel to first person
    travel1 = travel_times[(start_location, p1["location"])]
    arrive1 = arrival_time + travel1
    start1 = max(arrive1, p1["start_min"])
    max_dur1 = p1["end_min"] - start1
    if max_dur1 < p1["min_meet"]:
        return None  # cannot even meet p1

    best = None  # (total_met, total_meet_time, finish_time, itinerary)

    # Enumerate possible durations for first meeting
    for dur1 in range(p1["min_meet"], max_dur1 + 1):
        end1 = start1 + dur1

        # Travel to second person
        travel12 = travel_times[(p1["location"], p2["location"])]
        arrive2 = end1 + travel12
        start2 = max(arrive2, p2["start_min"])
        max_dur2 = p2["end_min"] - start2

        if max_dur2 >= p2["min_meet"]:
            dur2 = max_dur2  # maximize total meeting time
            end2 = start2 + dur2
            total_meet_time = dur1 + dur2
            itinerary = [
                {
                    "action": "meet",
                    "location": p1["location"],
                    "person": p1_name,
                    "start_time": fmt_time(start1),
                    "end_time": fmt_time(end1),
                },
                {
                    "action": "meet",
                    "location": p2["location"],
                    "person": p2_name,
                    "start_time": fmt_time(start2),
                    "end_time": fmt_time(end2),
                },
            ]
            candidate = (2, total_meet_time, end2, itinerary)
            if best is None or candidate > best:
                best = candidate

    return best

def compute_single(person_name):
    p = people[person_name]
    travel1 = travel_times[(start_location, p["location"])]
    arrive1 = arrival_time + travel1
    start1 = max(arrive1, p["start_min"])
    max_dur1 = p["end_min"] - start1
    if max_dur1 < p["min_meet"]:
        return None
    dur1 = max_dur1  # maximize meeting time since only single meeting
    end1 = start1 + dur1
    itinerary = [
        {
            "action": "meet",
            "location": p["location"],
            "person": person_name,
            "start_time": fmt_time(start1),
            "end_time": fmt_time(end1),
        }
    ]
    return (1, dur1, end1, itinerary)

def choose_best():
    candidates = []

    # Try both possible orders for meeting both people
    for order in permutations(people.keys(), 2):
        res = compute_two_order(order)
        if res:
            candidates.append(res)

    # If we cannot meet both, consider single-person schedules
    if not candidates:
        for person_name in people.keys():
            res = compute_single(person_name)
            if res:
                candidates.append(res)

    if not candidates:
        return {"itinerary": []}

    # Select best candidate:
    # Priority: maximize number met, then total meeting time, then earliest finish time (min),
    # implement earliest finish by sorting finish time ascending (we invert sign since tuple comparison uses max)
    # We will sort with custom key.
    def sort_key(item):
        total_met, total_meet_time, finish_time, _ = item
        return (total_met, total_meet_time, -finish_time)

    best = sorted(candidates, key=sort_key, reverse=True)[0]
    return {"itinerary": best[3]}

def main():
    result = choose_best()
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()