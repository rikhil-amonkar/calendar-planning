import json
from itertools import permutations

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02}"

def compute_schedule(order, travel_times, friends, start_time):
    current_time = start_time
    current_loc = "Bayview"
    itinerary = []
    total = 0
    
    for name in order:
        friend = next(f for f in friends if f["name"] == name)
        travel = travel_times.get((current_loc, friend["location"]), 0)
        arrive = current_time + travel
        start = max(arrive, friend["available_start"])
        end = min(friend["available_end"], start + friend["desired"])
        duration = end - start
        if duration <= 0:
            continue
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": name,
            "start_time": format_time(start),
            "end_time": format_time(end)
        })
        total += duration
        current_time = end
        current_loc = friend["location"]
    return itinerary, total

travel_times = {
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Presidio"): 31,
    ("Union Square", "Presidio"): 24,
    ("Presidio", "Union Square"): 22,
    ("Union Square", "Bayview"): 15,
    ("Presidio", "Bayview"): 31
}

friends = [
    {
        "name": "Richard",
        "location": "Union Square",
        "available_start": 8*60 +45,
        "available_end": 13*60,
        "desired": 120
    },
    {
        "name": "Charles",
        "location": "Presidio",
        "available_start": 9*60 +45,
        "available_end": 13*60,
        "desired": 120
    }
]

best = None
max_total = 0

for order in permutations(["Richard", "Charles"]):
    itinerary, total = compute_schedule(order, travel_times, friends, 9*60)
    if total > max_total:
        max_total = total
        best = itinerary

print(json.dumps({"itinerary": best}, indent=2))