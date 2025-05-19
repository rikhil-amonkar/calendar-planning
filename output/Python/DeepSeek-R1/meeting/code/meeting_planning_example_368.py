import itertools
import json

friends = [
    {'name': 'Joseph', 'location': 'Russian Hill', 'available_start': 510, 'available_end': 1155, 'duration': 60},
    {'name': 'Nancy', 'location': 'Alamo Square', 'available_start': 660, 'available_end': 960, 'duration': 90},
    {'name': 'Jason', 'location': 'North Beach', 'available_start': 1005, 'available_end': 1305, 'duration': 15},
    {'name': 'Jeffrey', 'location': 'Financial District', 'available_start': 630, 'available_end': 945, 'duration': 45}
]

travel_times = {
    'Bayview': {'Russian Hill':23,'Alamo Square':16,'North Beach':21,'Financial District':19},
    'Russian Hill': {'Bayview':23,'Alamo Square':15,'North Beach':5,'Financial District':11},
    'Alamo Square': {'Bayview':16,'Russian Hill':13,'North Beach':15,'Financial District':17},
    'North Beach': {'Bayview':22,'Russian Hill':4,'Alamo Square':16,'Financial District':8},
    'Financial District': {'Bayview':19,'Russian Hill':10,'Alamo Square':17,'North Beach':7}
}

valid = []
for k in range(4, 0, -1):
    for perm in itertools.permutations(friends, k):
        loc = 'Bayview'
        time = 540
        sched = []
        valid_perm = True
        for p in perm:
            travel = travel_times[loc][p['location']]
            arrive = time + travel
            start = max(arrive, p['available_start'])
            end = start + p['duration']
            if end > p['available_end']:
                valid_perm = False
                break
            sched.append((p, start, end))
            time = end
            loc = p['location']
        if valid_perm:
            valid.append((len(perm), time, sched))

best = []
max_friends = 0
min_end = float('inf')
for v in valid:
    if v[0] > max_friends or (v[0] == max_friends and v[1] < min_end):
        max_friends = v[0]
        min_end = v[1]
        best = v[2]

def fmt(m):
    h, m = divmod(m, 60)
    return f"{h}:{m:02d}"

itinerary = []
for meet in best:
    person = meet[0]
    itinerary.append({
        "action": "meet",
        "location": person['location'],
        "person": person['name'],
        "start_time": fmt(meet[1]),
        "end_time": fmt(meet[2])
    })

print(json.dumps({"itinerary": itinerary}, indent=2))