import itertools
import json
from typing import Dict, Tuple, List

# Helper functions
def parse_time(time_str: str) -> int:
    # Expects formats like '9:00AM', '7:45PM', '15:30' (24h optional without AM/PM)
    time_str = time_str.strip().upper()
    if time_str.endswith('AM') or time_str.endswith('PM'):
        meridiem = time_str[-2:]
        hh_mm = time_str[:-2]
        hour_str, minute_str = hh_mm.split(':')
        hour = int(hour_str)
        minute = int(minute_str)
        if meridiem == 'AM':
            if hour == 12:
                hour = 0
        else:  # PM
            if hour != 12:
                hour += 12
        return hour * 60 + minute
    else:
        # 24-hour format "H:MM" or "HH:MM"
        hour_str, minute_str = time_str.split(':')
        return int(hour_str) * 60 + int(minute_str)

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (constraints and travel times)
start_location = "Bayview"
start_time_str = "9:00AM"

people = [
    {
        "name": "Betty",
        "location": "Embarcadero",
        "available_start": "7:45PM",
        "available_end": "9:45PM",
        "min_duration": 15
    },
    {
        "name": "Karen",
        "location": "Fisherman's Wharf",
        "available_start": "8:45AM",
        "available_end": "3:00PM",
        "min_duration": 30
    },
    {
        "name": "Anthony",
        "location": "Financial District",
        "available_start": "9:15AM",
        "available_end": "9:30PM",
        "min_duration": 105
    }
]

# Directed travel times in minutes
travel_times: Dict[Tuple[str, str], int] = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Financial District"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Financial District"): 5,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Fisherman's Wharf"): 10,
}

def get_travel_time(a: str, b: str) -> int:
    if a == b:
        return 0
    return travel_times[(a, b)]

# Convert input time strings to minutes
start_time = parse_time(start_time_str)
for p in people:
    p["avail_start_min"] = parse_time(p["available_start"])
    p["avail_end_min"] = parse_time(p["available_end"])

# Scheduling logic
def compute_schedule(order: List[dict]) -> Tuple[bool, List[dict], int, int, int]:
    itinerary = []
    cur_loc = start_location
    cur_time = start_time
    total_wait = 0
    total_travel = 0

    for person in order:
        travel = get_travel_time(cur_loc, person["location"])
        arrival = cur_time + travel
        total_travel += travel

        start_meet = max(arrival, person["avail_start_min"])
        wait = max(0, start_meet - arrival)
        total_wait += wait

        end_meet = start_meet + person["min_duration"]

        if end_meet > person["avail_end_min"]:
            return False, [], 0, 0, 0  # infeasible

        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet),
        })

        cur_loc = person["location"]
        cur_time = end_meet

    return True, itinerary, cur_time, total_wait, total_travel

# Explore all possible schedules to maximize number of people met
best = None  # tuple: (-count, end_time, total_wait, total_travel, itinerary)
names_to_person = {p["name"]: p for p in people}

for r in range(len(people), 0, -1):  # prioritize largest number of friends
    found_for_r = []
    for subset in itertools.combinations(people, r):
        for order in itertools.permutations(subset):
            feasible, itinerary, end_time, total_wait, total_travel = compute_schedule(list(order))
            if feasible:
                score = (-len(order), end_time, total_wait, total_travel)
                found_for_r.append((score, itinerary))
    if found_for_r:
        # Choose best by minimizing end_time, then waiting, then travel
        found_for_r.sort(key=lambda x: x[0])
        best = found_for_r[0][1]
        break

result = {"itinerary": best if best is not None else []}

print(json.dumps(result, ensure_ascii=False, indent=2))