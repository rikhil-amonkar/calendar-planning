import itertools
import json
from collections import namedtuple

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02}"

Friend = namedtuple('Friend', ['name', 'location', 'start', 'end', 'min_duration'])

travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Union Square"): 22
}

friends = [
    Friend("Karen", "Russian Hill", 20*60+45, 21*60+45, 60),
    Friend("Jessica", "The Castro", 15*60+45, 19*60+30, 60),
    Friend("Matthew", "Richmond District", 7*60+30, 15*60+15, 15),
    Friend("Michelle", "Marina District", 10*60+30, 18*60+45, 75),
    Friend("Carol", "North Beach", 12*60, 17*60, 90),
    Friend("Stephanie", "Union Square", 10*60+45, 14*60+15, 30),
    Friend("Linda", "Golden Gate Park", 10*60+45, 22*60, 90)
]

start_time = 540
start_location = "Sunset District"
best_itinerary = None
found = False

for size in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, size):
        for perm in itertools.permutations(subset):
            current_time = start_time
            current_loc = start_location
            itinerary = []
            valid = True
            for friend in perm:
                key = (current_loc, friend.location)
                travel = travel_times[key]
                arrival = current_time + travel
                start_meet = max(arrival, friend.start)
                if start_meet + friend.min_duration > friend.end:
                    valid = False
                    break
                end_meet = start_meet + friend.min_duration
                itinerary.append((friend.name, friend.location, start_meet, end_meet))
                current_time = end_meet
                current_loc = friend.location
            if valid:
                best_itinerary = itinerary
                found = True
                break
        if found:
            break
    if found:
        break

result = []
if best_itinerary:
    for name, loc, start_min, end_min in best_itinerary:
        result.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": format_time(start_min),
            "end_time": format_time(end_min)
        })

output = {"itinerary": result}
print(json.dumps(output))