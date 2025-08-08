from z3 import *
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

travel_times = {
    "Bayview": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 25,
        "Financial District": 19
    },
    "Embarcadero": {
        "Bayview": 21,
        "Fisherman's Wharf": 6,
        "Financial District": 5
    },
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Embarcadero": 8,
        "Financial District": 11
    },
    "Financial District": {
        "Bayview": 19,
        "Embarcadero": 4,
        "Fisherman's Wharf": 10
    }
}

friends = {
    "Karen": {
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("08:45"),
        "avail_end": time_to_minutes("15:00"),
        "min_duration": 30
    },
    "Anthony": {
        "location": "Financial District",
        "avail_start": time_to_minutes("09:15"),
        "avail_end": time_to_minutes("21:30"),
        "min_duration": 105
    },
    "Betty": {
        "location": "Embarcadero",
        "avail_start": time_to_minutes("19:45"),
        "avail_end": time_to_minutes("21:45"),
        "min_duration": 15
    }
}

k_start = Int('k_start')
k_end = Int('k_end')
a_start = Int('a_start')
a_end = Int('a_end')
b_start = Int('b_start')
b_end = Int('b_end')

first = Int('first')
second = Int('second')
third = Int('third')

s = Solver()

friend_indices = {"Karen": 0, "Anthony": 1, "Betty": 2}
friend_names = {0: "Karen", 1: "Anthony", 2: "Betty"}

s.add(And(first >= 0, first <= 2))
s.add(And(second >= 0, second <= 2))
s.add(And(third >= 0, third <= 2))
s.add(Distinct(first, second, third))

s.add(k_end - k_start >= friends["Karen"]["min_duration"])
s.add(a_end - a_start >= friends["Anthony"]["min_duration"])
s.add(b_end - b_start >= friends["Betty"]["min_duration"])

s.add(k_start >= friends["Karen"]["avail_start"])
s.add(k_end <= friends["Karen"]["avail_end"])
s.add(a_start >= friends["Anthony"]["avail_start"])
s.add(a_end <= friends["Anthony"]["avail_end"])
s.add(b_start >= friends["Betty"]["avail_start"])
s.add(b_end <= friends["Betty"]["avail_end"])

start_time = 540  # 9:00 AM in minutes

s.add(Or(
    And(first == 0, k_start >= start_time + travel_times["Bayview"][friends["Karen"]["location"]]),
    And(first == 1, a_start >= start_time + travel_times["Bayview"][friends["Anthony"]["location"]]),
    And(first == 2, b_start >= start_time + travel_times["Bayview"][friends["Betty"]["location"]])
))

s.add(Or(
    And(first == 0, second == 1, a_start >= k_end + travel_times[friends["Karen"]["location"]][friends["Anthony"]["location"]]),
    And(first == 0, second == 2, b_start >= k_end + travel_times[friends["Karen"]["location"]][friends["Betty"]["location"]]),
    And(first == 1, second == 0, k_start >= a_end + travel_times[friends["Anthony"]["location"]][friends["Karen"]["location"]]),
    And(first == 1, second == 2, b_start >= a_end + travel_times[friends["Anthony"]["location"]][friends["Betty"]["location"]]),
    And(first == 2, second == 0, k_start >= b_end + travel_times[friends["Betty"]["location"]][friends["Karen"]["location"]]),
    And(first == 2, second == 1, a_start >= b_end + travel_times[friends["Betty"]["location"]][friends["Anthony"]["location"]])
))

s.add(Or(
    And(second == 0, third == 1, a_start >= k_end + travel_times[friends["Karen"]["location"]][friends["Anthony"]["location"]]),
    And(second == 0, third == 2, b_start >= k_end + travel_times[friends["Karen"]["location"]][friends["Betty"]["location"]]),
    And(second == 1, third == 0, k_start >= a_end + travel_times[friends["Anthony"]["location"]][friends["Karen"]["location"]]),
    And(second == 1, third == 2, b_start >= a_end + travel_times[friends["Anthony"]["location"]][friends["Betty"]["location"]]),
    And(second == 2, third == 0, k_start >= b_end + travel_times[friends["Betty"]["location"]][friends["Karen"]["location"]]),
    And(second == 2, third == 1, a_start >= b_end + travel_times[friends["Betty"]["location"]][friends["Anthony"]["location"]])
))

if s.check() == sat:
    model = s.model()
    k_start_val = model.eval(k_start).as_long()
    k_end_val = model.eval(k_end).as_long()
    a_start_val = model.eval(a_start).as_long()
    a_end_val = model.eval(a_end).as_long()
    b_start_val = model.eval(b_start).as_long()
    b_end_val = model.eval(b_end).as_long()
    
    meetings = [
        {"person": "Karen", "start": k_start_val, "end": k_end_val},
        {"person": "Anthony", "start": a_start_val, "end": a_end_val},
        {"person": "Betty", "start": b_start_val, "end": b_end_val}
    ]
    
    meetings_sorted = sorted(meetings, key=lambda x: x['start'])
    
    itinerary = []
    for meet in meetings_sorted:
        itinerary.append({
            "action": "meet",
            "person": meet["person"],
            "start_time": minutes_to_time(meet["start"]),
            "end_time": minutes_to_time(meet["end"])
        })
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No valid schedule found.")