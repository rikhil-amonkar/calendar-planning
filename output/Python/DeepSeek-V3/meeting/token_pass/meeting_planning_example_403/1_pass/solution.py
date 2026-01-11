import itertools
import json

def time_to_min(t):
    # t is string like "9:00" or "13:30"
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times matrix
locations = ["US", "GGP", "PH", "P", "CT", "TC"]
loc_index = {loc: i for i, loc in enumerate(locations)}

travel = [
    [0, 22, 15, 24, 7, 19],   # US
    [22, 0, 16, 11, 23, 13],  # GGP
    [12, 15, 0, 11, 11, 16],  # PH
    [22, 12, 11, 0, 21, 21],  # P
    [7, 23, 10, 19, 0, 22],   # CT
    [19, 11, 16, 20, 20, 0]   # TC
]

# Friends data: name, location, start_min, end_min, min_duration
friends = [
    ("Andrew", "GGP", time_to_min("11:45"), time_to_min("14:30"), 75),
    ("Sarah", "PH", time_to_min("16:15"), time_to_min("18:45"), 15),
    ("Nancy", "P", time_to_min("17:30"), time_to_min("19:15"), 60),
    ("Rebecca", "CT", time_to_min("9:45"), time_to_min("21:30"), 90),
    ("Robert", "TC", time_to_min("8:30"), time_to_min("14:15"), 30)
]

# Adjust Robert's start to 9:00 if earlier (since we start at 9:00)
robert_idx = 4
friends = list(friends)
f = list(friends[robert_idx])
f[2] = max(time_to_min("9:00"), f[2])  # start at 9:00 or later
friends[robert_idx] = tuple(f)

# We start at US at 9:00 (0 min)
start_time = 0
start_loc = "US"

best_count = 0
best_schedule = []

# Try meeting all 5, then 4, etc.
for k in range(5, 0, -1):
    for subset in itertools.combinations(range(5), k):
        for perm in itertools.permutations(subset):
            current_loc = start_loc
            current_time = start_time
            schedule = []
            possible = True
            
            for idx in perm:
                name, loc, win_start, win_end, dur = friends[idx]
                travel_time = travel[loc_index[current_loc]][loc_index[loc]]
                arrive_time = current_time + travel_time
                start_meeting = max(arrive_time, win_start)
                if start_meeting + dur > win_end:
                    possible = False
                    break
                schedule.append((name, loc, start_meeting, start_meeting + dur))
                current_time = start_meeting + dur
                current_loc = loc
            
            if possible and k > best_count:
                best_count = k
                best_schedule = schedule
                # We want maximal number, so first found for max k is fine
                # but we could keep searching for better total time, but not required
                break
        if best_count == k and best_schedule:
            break
    if best_count == k and best_schedule:
        break

# Convert to required JSON
itinerary = []
for name, loc, start_m, end_m in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": {
            "GGP": "Golden Gate Park",
            "PH": "Pacific Heights",
            "P": "Presidio",
            "CT": "Chinatown",
            "TC": "The Castro",
            "US": "Union Square"
        }[loc],
        "person": name,
        "start_time": min_to_time(start_m),
        "end_time": min_to_time(end_m)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))