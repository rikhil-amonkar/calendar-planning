from z3 import *
import json

def time_to_minutes(t):
    parts = t.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

travel_dict = {
    "Nob Hill": {
        "Embarcadero": 9, "The Castro": 17, "Haight-Ashbury": 13, "Union Square": 7, "North Beach": 8,
        "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 17, "Marina District": 11, "Russian Hill": 5
    },
    "Embarcadero": {
        "Nob Hill": 10, "The Castro": 25, "Haight-Ashbury": 21, "Union Square": 10, "North Beach": 5,
        "Pacific Heights": 11, "Chinatown": 7, "Golden Gate Park": 25, "Marina District": 12, "Russian Hill": 8
    },
    "The Castro": {
        "Nob Hill": 16, "Embarcadero": 22, "Haight-Ashbury": 6, "Union Square": 19, "North Beach": 20,
        "Pacific Heights": 16, "Chinatown": 22, "Golden Gate Park": 11, "Marina District": 21, "Russian Hill": 18
    },
    "Haight-Ashbury": {
        "Nob Hill": 15, "Embarcadero": 20, "The Castro": 6, "Union Square": 19, "North Beach": 19,
        "Pacific Heights": 12, "Chinatown": 19, "Golden Gate Park": 7, "Marina District": 17, "Russian Hill": 17
    },
    "Union Square": {
        "Nob Hill": 9, "Embarcadero": 11, "The Castro": 17, "Haight-Ashbury": 18, "North Beach": 10,
        "Pacific Heights": 15, "Chinatown": 7, "Golden Gate Park": 22, "Marina District": 18, "Russian Hill": 13
    },
    "North Beach": {
        "Nob Hill": 7, "Embarcadero": 6, "The Castro": 23, "Haight-Ashbury": 18, "Union Square": 7,
        "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 22, "Marina District": 9, "Russian Hill": 4
    },
    "Pacific Heights": {
        "Nob Hill": 8, "Embarcadero": 10, "The Castro": 16, "Haight-Ashbury": 11, "Union Square": 12,
        "North Beach": 9, "Chinatown": 11, "Golden Gate Park": 15, "Marina District": 6, "Russian Hill": 7
    },
    "Chinatown": {
        "Nob Hill": 9, "Embarcadero": 5, "The Castro": 22, "Haight-Ashbury": 19, "Union Square": 7,
        "North Beach": 3, "Pacific Heights": 10, "Golden Gate Park": 23, "Marina District": 12, "Russian Hill": 7
    },
    "Golden Gate Park": {
        "Nob Hill": 20, "Embarcadero": 25, "The Castro": 13, "Haight-Ashbury": 7, "Union Square": 22,
        "North Beach": 23, "Pacific Heights": 16, "Chinatown": 23, "Marina District": 16, "Russian Hill": 19
    },
    "Marina District": {
        "Nob Hill": 12, "Embarcadero": 14, "The Castro": 22, "Haight-Ashbury": 16, "Union Square": 16,
        "North Beach": 11, "Pacific Heights": 7, "Chinatown": 15, "Golden Gate Park": 18, "Russian Hill": 8
    },
    "Russian Hill": {
        "Nob Hill": 5, "Embarcadero": 8, "The Castro": 21, "Haight-Ashbury": 17, "Union Square": 10,
        "North Beach": 5, "Pacific Heights": 7, "Chinatown": 9, "Golden Gate Park": 21, "Marina District": 7
    }
}

meetings = [
    {"name": "Start", "loc": "Nob Hill", "start": 540, "end": 540, "min_dur": 0},
    {"name": "Mary", "loc": "Embarcadero", "start": time_to_minutes("20:00"), "end": time_to_minutes("21:15"), "min_dur": 75},
    {"name": "Kenneth", "loc": "The Castro", "start": time_to_minutes("11:15"), "end": time_to_minutes("19:15"), "min_dur": 30},
    {"name": "Joseph", "loc": "Haight-Ashbury", "start": time_to_minutes("20:00"), "end": time_to_minutes("22:00"), "min_dur": 120},
    {"name": "Sarah", "loc": "Union Square", "start": time_to_minutes("11:45"), "end": time_to_minutes("14:30"), "min_dur": 90},
    {"name": "Thomas", "loc": "North Beach", "start": time_to_minutes("19:15"), "end": time_to_minutes("19:45"), "min_dur": 15},
    {"name": "Daniel", "loc": "Pacific Heights", "start": time_to_minutes("13:45"), "end": time_to_minutes("20:30"), "min_dur": 15},
    {"name": "Richard", "loc": "Chinatown", "start": time_to_minutes("08:00"), "end": time_to_minutes("18:45"), "min_dur": 30},
    {"name": "Mark", "loc": "Golden Gate Park", "start": time_to_minutes("17:30"), "end": time_to_minutes("21:30"), "min_dur": 120},
    {"name": "David", "loc": "Marina District", "start": time_to_minutes("20:00"), "end": time_to_minutes("21:00"), "min_dur": 60},
    {"name": "Karen", "loc": "Russian Hill", "start": time_to_minutes("13:15"), "end": time_to_minutes("18:30"), "min_dur": 120}
]

opt = Optimize()

meet = [None] * 11
s_time = [None] * 11
e_time = [None] * 11

for i in range(11):
    if i == 0:
        meet[0] = True
        s_time[0] = 540
        e_time[0] = 540
    else:
        meet[i] = Bool(f'meet_{i}')
        s_time[i] = Int(f's_{i}')
        e_time[i] = Int(f'e_{i}')

for i in range(1, 11):
    opt.add(Implies(meet[i], s_time[i] >= meetings[i]["start"]))
    opt.add(Implies(meet[i], e_time[i] <= meetings[i]["end"]))
    opt.add(Implies(meet[i], e_time[i] - s_time[i] >= meetings[i]["min_dur"]))

for i in range(11):
    for j in range(i+1, 11):
        held_i = meet[i] if i >= 1 else True
        held_j = meet[j] if j >= 1 else True
        condition = And(held_i, held_j)
        
        loc_i = meetings[i]["loc"]
        loc_j = meetings[j]["loc"]
        travel_ij = travel_dict[loc_i][loc_j]
        travel_ji = travel_dict[loc_j][loc_i]
        
        constraint = Or(
            s_time[i] >= e_time[j] + travel_ji,
            s_time[j] >= e_time[i] + travel_ij
        )
        opt.add(Implies(condition, constraint))

objective = Sum([If(meet[i], 1, 0) for i in range(1, 11)])
opt.maximize(objective)

if opt.check() == sat:
    model = opt.model()
    itinerary_list = []
    for i in range(1, 11):
        if is_true(model[meet[i]]):
            s_val = model[s_time[i]].as_long()
            e_val = model[e_time[i]].as_long()
            start_str = minutes_to_time(s_val)
            end_str = minutes_to_time(e_val)
            itinerary_list.append({
                "action": "meet",
                "person": meetings[i]["name"],
                "start_time": start_str,
                "end_time": end_str
            })
    itinerary_list.sort(key=lambda x: time_to_minutes(x["start_time"]))
    result = {"itinerary": itinerary_list}
    print("SOLUTION:")
    print(json.dumps(result))
else:
    print("No solution found")