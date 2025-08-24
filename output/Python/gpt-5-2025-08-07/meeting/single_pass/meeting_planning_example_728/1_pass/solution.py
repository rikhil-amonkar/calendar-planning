import itertools
import json

# Input variables: locations, travel times (minutes), availability windows, and minimum meeting durations

locations = [
    "Marina District",
    "Mission District",
    "Fisherman's Wharf",
    "Presidio",
    "Union Square",
    "Sunset District",
    "Financial District",
    "Haight-Ashbury",
    "Russian Hill",
]

# Directed travel times in minutes
travel = {
    "Marina District": {
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Presidio": 10,
        "Union Square": 16,
        "Sunset District": 19,
        "Financial District": 17,
        "Haight-Ashbury": 16,
        "Russian Hill": 8,
    },
    "Mission District": {
        "Marina District": 19,
        "Fisherman's Wharf": 22,
        "Presidio": 25,
        "Union Square": 15,
        "Sunset District": 24,
        "Financial District": 15,
        "Haight-Ashbury": 12,
        "Russian Hill": 15,
    },
    "Fisherman's Wharf": {
        "Marina District": 9,
        "Mission District": 22,
        "Presidio": 17,
        "Union Square": 13,
        "Sunset District": 27,
        "Financial District": 11,
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
    },
    "Presidio": {
        "Marina District": 11,
        "Mission District": 26,
        "Fisherman's Wharf": 19,
        "Union Square": 22,
        "Sunset District": 15,
        "Financial District": 23,
        "Haight-Ashbury": 15,
        "Russian Hill": 14,
    },
    "Union Square": {
        "Marina District": 18,
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Presidio": 24,
        "Sunset District": 27,
        "Financial District": 9,
        "Haight-Ashbury": 18,
        "Russian Hill": 13,
    },
    "Sunset District": {
        "Marina District": 21,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Presidio": 16,
        "Union Square": 30,
        "Financial District": 30,
        "Haight-Ashbury": 15,
        "Russian Hill": 24,
    },
    "Financial District": {
        "Marina District": 15,
        "Mission District": 17,
        "Fisherman's Wharf": 10,
        "Presidio": 22,
        "Union Square": 9,
        "Sunset District": 30,
        "Haight-Ashbury": 19,
        "Russian Hill": 11,
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Mission District": 11,
        "Fisherman's Wharf": 23,
        "Presidio": 15,
        "Union Square": 19,
        "Sunset District": 15,
        "Financial District": 21,
        "Russian Hill": 17,
    },
    "Russian Hill": {
        "Marina District": 7,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Presidio": 14,
        "Union Square": 10,
        "Sunset District": 23,
        "Financial District": 11,
        "Haight-Ashbury": 17,
    },
}

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# People constraints: name, location, availability window [start,end], minimum meeting duration (minutes)
people = [
    {
        "name": "Karen",
        "location": "Mission District",
        "start": to_minutes(14, 15),
        "end": to_minutes(22, 0),
        "duration": 30,
    },
    {
        "name": "Richard",
        "location": "Fisherman's Wharf",
        "start": to_minutes(14, 30),
        "end": to_minutes(17, 30),
        "duration": 30,
    },
    {
        "name": "Robert",
        "location": "Presidio",
        "start": to_minutes(21, 45),
        "end": to_minutes(22, 45),
        "duration": 60,
    },
    {
        "name": "Joseph",
        "location": "Union Square",
        "start": to_minutes(11, 45),
        "end": to_minutes(14, 45),
        "duration": 120,
    },
    {
        "name": "Helen",
        "location": "Sunset District",
        "start": to_minutes(14, 45),
        "end": to_minutes(20, 45),
        "duration": 105,
    },
    {
        "name": "Elizabeth",
        "location": "Financial District",
        "start": to_minutes(10, 0),
        "end": to_minutes(12, 45),
        "duration": 75,
    },
    {
        "name": "Kimberly",
        "location": "Haight-Ashbury",
        "start": to_minutes(14, 15),
        "end": to_minutes(17, 30),
        "duration": 105,
    },
    {
        "name": "Ashley",
        "location": "Russian Hill",
        "start": to_minutes(11, 30),
        "end": to_minutes(21, 30),
        "duration": 45,
    },
]

start_time = to_minutes(9, 0)
start_location = "Marina District"

def schedule_for_order(order):
    current_time = start_time
    current_loc = start_location
    itinerary = []
    total_travel = 0
    total_wait = 0

    for person in order:
        loc = person["location"]
        # Travel time from current_loc to loc
        t_travel = travel[current_loc][loc] if current_loc != loc else 0
        arrival = current_time + t_travel
        # Earliest feasible start (can wait)
        start = max(arrival, person["start"])
        end = start + person["duration"]
        # Check feasibility
        if end <= person["end"]:
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": person["name"],
                "start_time": start,
                "end_time": end,
                "travel_in": t_travel,
                "wait": max(0, person["start"] - arrival),
            })
            total_travel += t_travel
            total_wait += max(0, person["start"] - arrival)
            current_time = end
            current_loc = loc
        else:
            # Skip this person if infeasible in this order
            continue

    return itinerary, total_travel, total_wait

def evaluate_itinerary(itinerary, total_travel, total_wait):
    if itinerary:
        finish_time = itinerary[-1]["end_time"]
    else:
        finish_time = start_time
    count = len(itinerary)
    total_meeting_minutes = sum(item["end_time"] - item["start_time"] for item in itinerary)
    # Objective: maximize count, then maximize meeting minutes (though fixed mins), 
    # then minimize finish time, then minimize wait, then minimize travel
    return (
        count,
        total_meeting_minutes,
        -finish_time,          # earlier finish is better -> larger negative is better in max comparison
        -total_wait,           # less wait is better
        -total_travel          # less travel is better
    )

best_itinerary = []
best_score = None
best_meta = (0, 0)  # travel, wait

# Try all permutations (8! = 40320)
for order in itertools.permutations(people):
    itinerary, total_travel, total_wait = schedule_for_order(order)
    score = evaluate_itinerary(itinerary, total_travel, total_wait)
    if (best_score is None) or (score > best_score):
        best_score = score
        best_itinerary = itinerary
        best_meta = (total_travel, total_wait)

# Convert itinerary times to strings and strip helper fields
output_itinerary = []
for item in best_itinerary:
    output_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start_time"]),
        "end_time": fmt_time(item["end_time"]),
    })

result = {"itinerary": output_itinerary}

print(json.dumps(result, ensure_ascii=False, indent=2))