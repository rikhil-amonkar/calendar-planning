from z3 import *

def min_to_time(total_minutes):
    total_minutes = int(total_minutes)
    hours = total_minutes // 60
    minutes = total_minutes % 60
    abs_hour = 9 + hours
    abs_minute = minutes
    return f"{abs_hour:02d}:{abs_minute:02d}"

districts = [
    "Marina District",
    "Mission District",
    "Fisherman's Wharf",
    "Presidio",
    "Union Square",
    "Sunset District",
    "Financial District",
    "Haight-Ashbury",
    "Russian Hill"
]

travel_time_dict = {
    ('Marina District', 'Mission District'): 20,
    ('Marina District', "Fisherman's Wharf"): 10,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', "Fisherman's Wharf"): 22,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Russian Hill'): 15,
    ("Fisherman's Wharf", 'Marina District'): 9,
    ("Fisherman's Wharf", 'Mission District'): 22,
    ("Fisherman's Wharf", 'Presidio'): 17,
    ("Fisherman's Wharf", 'Union Square'): 13,
    ("Fisherman's Wharf", 'Sunset District'): 27,
    ("Fisherman's Wharf", 'Financial District'): 11,
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ("Fisherman's Wharf", 'Russian Hill'): 7,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', "Fisherman's Wharf"): 19,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', "Fisherman's Wharf"): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Russian Hill'): 13,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', "Fisherman's Wharf"): 29,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Russian Hill'): 24,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', "Fisherman's Wharf"): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Russian Hill'): 11,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', "Fisherman's Wharf"): 7,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Haight-Ashbury'): 17
}

for d in districts:
    travel_time_dict[(d, d)] = 0

friends = [
    {"name": "Karen", "district": "Mission District", "avail_start": 315, "avail_end": 780, "min_duration": 30},
    {"name": "Richard", "district": "Fisherman's Wharf", "avail_start": 330, "avail_end": 510, "min_duration": 30},
    {"name": "Robert", "district": "Presidio", "avail_start": 765, "avail_end": 825, "min_duration": 60},
    {"name": "Joseph", "district": "Union Square", "avail_start": 165, "avail_end": 345, "min_duration": 120},
    {"name": "Helen", "district": "Sunset District", "avail_start": 345, "avail_end": 705, "min_duration": 105},
    {"name": "Elizabeth", "district": "Financial District", "avail_start": 60, "avail_end": 225, "min_duration": 75},
    {"name": "Kimberly", "district": "Haight-Ashbury", "avail_start": 315, "avail_end": 510, "min_duration": 105},
    {"name": "Ashley", "district": "Russian Hill", "avail_start": 150, "avail_end": 750, "min_duration": 45}
]

solver = Optimize()
n = len(friends)
include = [Bool(f"include_{i}") for i in range(n)]
s = [Int(f"s_{i}") for i in range(n)]
e = [Int(f"e_{i}") for i in range(n)]

for i in range(n):
    solver.add(Implies(include[i], e[i] == s[i] + friends[i]["min_duration"]))
    solver.add(Implies(include[i], s[i] >= friends[i]["avail_start"]))
    solver.add(Implies(include[i], e[i] <= friends[i]["avail_end"]))
    from_marina = travel_time_dict[("Marina District", friends[i]["district"])]
    solver.add(Implies(include[i], s[i] >= from_marina))

for i in range(n):
    for j in range(i + 1, n):
        district_i = friends[i]["district"]
        district_j = friends[j]["district"]
        travel_ij = travel_time_dict[(district_i, district_j)]
        travel_ji = travel_time_dict[(district_j, district_i)]
        solver.add(Implies(And(include[i], include[j]),
                            Or(e[i] + travel_ij <= s[j], e[j] + travel_ji <= s[i])))

total_meetings = Sum([If(include[i], 1, 0) for i in range(n)])
solver.maximize(total_meetings)

if solver.check() == sat:
    model = solver.model()
    scheduled_meetings = []
    for i in range(n):
        if model.evaluate(include[i]):
            start_val = model.evaluate(s[i])
            end_val = model.evaluate(e[i])
            if is_int_value(start_val) and is_int_value(end_val):
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                start_time = min_to_time(start_min)
                end_time = min_to_time(end_min)
                scheduled_meetings.append({
                    "person": friends[i]["name"],
                    "start": start_min,
                    "start_time": start_time,
                    "end_time": end_time
                })
    scheduled_meetings_sorted = sorted(scheduled_meetings, key=lambda x: x["start"])
    itinerary_list = []
    for meet in scheduled_meetings_sorted:
        itinerary_list.append({
            "action": "meet",
            "person": meet["person"],
            "start_time": meet["start_time"],
            "end_time": meet["end_time"]
        })
    result = {"itinerary": itinerary_list}
    print(f"SOLUTION: {result}")
else:
    print("SOLUTION: {\"itinerary\": []}")