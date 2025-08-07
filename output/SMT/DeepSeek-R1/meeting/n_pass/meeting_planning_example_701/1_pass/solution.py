import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

friends = [
    ("Lisa", "The Castro", (19*60+15, 21*60+15), 120),
    ("Daniel", "Nob Hill", (8*60+15, 11*60), 15),
    ("Elizabeth", "Presidio", (21*60+15, 22*60+15), 45),
    ("Steven", "Marina District", (16*60+30, 20*60+45), 90),
    ("Timothy", "Pacific Heights", (12*60, 18*60), 90),
    ("Ashley", "Golden Gate Park", (20*60+45, 21*60+45), 60),
    ("Kevin", "Chinatown", (12*60, 19*60), 30),
    ("Betty", "Richmond District", (13*60+15, 15*60+45), 30)
]

travel_dict = {
    "Mission District": {
        "The Castro": 7,
        "Nob Hill": 12,
        "Presidio": 25,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "Chinatown": 16,
        "Richmond District": 20
    },
    "The Castro": {
        "Mission District": 7,
        "Nob Hill": 16,
        "Presidio": 20,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Chinatown": 22,
        "Richmond District": 16
    },
    "Nob Hill": {
        "Mission District": 13,
        "The Castro": 17,
        "Presidio": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Chinatown": 6,
        "Richmond District": 14
    },
    "Presidio": {
        "Mission District": 26,
        "The Castro": 21,
        "Nob Hill": 18,
        "Marina District": 11,
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7
    },
    "Marina District": {
        "Mission District": 20,
        "The Castro": 22,
        "Nob Hill": 12,
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Chinatown": 15,
        "Richmond District": 11
    },
    "Pacific Heights": {
        "Mission District": 15,
        "The Castro": 16,
        "Nob Hill": 8,
        "Presidio": 11,
        "Marina District": 6,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Richmond District": 12
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "The Castro": 13,
        "Nob Hill": 20,
        "Presidio": 11,
        "Marina District": 16,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Richmond District": 7
    },
    "Chinatown": {
        "Mission District": 17,
        "The Castro": 22,
        "Nob Hill": 9,
        "Presidio": 19,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Golden Gate Park": 23,
        "Richmond District": 20
    },
    "Richmond District": {
        "Mission District": 20,
        "The Castro": 16,
        "Nob Hill": 17,
        "Presidio": 7,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Chinatown": 20
    }
}

daniel_index = 1
all_indices = list(range(8))
best_schedule = None
best_size = 0

for size in range(8, 0, -1):
    found = False
    for subset in itertools.combinations(all_indices, size):
        if daniel_index in subset:
            remaining = list(subset)
            remaining.remove(daniel_index)
            perms = itertools.permutations(remaining)
            for perm_rest in perms:
                perm = (daniel_index,) + perm_rest
                current_location = "Mission District"
                current_time = 540
                schedule = []
                valid = True
                for idx in perm:
                    meeting = friends[idx]
                    from_loc = current_location
                    to_loc = meeting[1]
                    travel_time_val = travel_dict[from_loc][to_loc]
                    current_time += travel_time_val
                    avail_start, avail_end = meeting[2]
                    if current_time < avail_start:
                        current_time = avail_start
                    start_time = current_time
                    end_time = start_time + meeting[3]
                    if end_time > avail_end:
                        valid = False
                        break
                    schedule.append((idx, start_time, end_time))
                    current_time = end_time
                    current_location = to_loc
                if valid:
                    best_schedule = schedule
                    best_size = size
                    found = True
                    break
            if found:
                break
        else:
            for perm in itertools.permutations(subset):
                current_location = "Mission District"
                current_time = 540
                schedule = []
                valid = True
                for idx in perm:
                    meeting = friends[idx]
                    from_loc = current_location
                    to_loc = meeting[1]
                    travel_time_val = travel_dict[from_loc][to_loc]
                    current_time += travel_time_val
                    avail_start, avail_end = meeting[2]
                    if current_time < avail_start:
                        current_time = avail_start
                    start_time = current_time
                    end_time = start_time + meeting[3]
                    if end_time > avail_end:
                        valid = False
                        break
                    schedule.append((idx, start_time, end_time))
                    current_time = end_time
                    current_location = to_loc
                if valid:
                    best_schedule = schedule
                    best_size = size
                    found = True
                    break
            if found:
                break
    if found:
        break

itinerary = []
if best_schedule:
    for (idx, start_time, end_time) in best_schedule:
        name = friends[idx][0]
        start_str = minutes_to_time(start_time)
        end_str = minutes_to_time(end_time)
        itinerary.append({"action": "meet", "person": name, "start_time": start_str, "end_time": end_str})

result = {"itinerary": itinerary}
print("SOLUTION:")
print(json.dumps(result))