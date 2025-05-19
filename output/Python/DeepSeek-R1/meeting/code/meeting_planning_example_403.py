import itertools
import json

def time_to_str(m):
    return f"{m//60}:{m%60:02d}"

friends = [
    {'name':'Andrew', 'location':'Golden Gate Park', 'start':705, 'end':870, 'duration':75},
    {'name':'Sarah', 'location':'Pacific Heights', 'start':975, 'end':1125, 'duration':15},
    {'name':'Nancy', 'location':'Presidio', 'start':1050, 'end':1155, 'duration':60},
    {'name':'Rebecca', 'location':'Chinatown', 'start':585, 'end':1290, 'duration':90},
    {'name':'Robert', 'location':'The Castro', 'start':510, 'end':855, 'duration':30}
]

travel = {
    'Union Square': {'Golden Gate Park':22, 'Pacific Heights':15, 'Presidio':24, 'Chinatown':7, 'The Castro':19},
    'Golden Gate Park': {'Union Square':22, 'Pacific Heights':16, 'Presidio':11, 'Chinatown':23, 'The Castro':13},
    'Pacific Heights': {'Union Square':12, 'Golden Gate Park':15, 'Presidio':11, 'Chinatown':11, 'The Castro':16},
    'Presidio': {'Union Square':22, 'Golden Gate Park':12, 'Pacific Heights':11, 'Chinatown':21, 'The Castro':21},
    'Chinatown': {'Union Square':7, 'Golden Gate Park':23, 'Pacific Heights':10, 'Presidio':19, 'The Castro':22},
    'The Castro': {'Union Square':19, 'Golden Gate Park':11, 'Pacific Heights':16, 'Presidio':20, 'Chinatown':20}
}

best = []
max_count = 0

for perm in itertools.permutations(friends):
    time = 540
    loc = 'Union Square'
    sched = []
    valid = True
    for p in perm:
        tt = travel[loc].get(p['location'], 999)
        arrive = time + tt
        start = max(arrive, p['start'])
        end = start + p['duration']
        if end > p['end']:
            valid = False
            break
        sched.append({'n':p['name'], 'l':p['location'], 's':start, 'e':end})
        time = end
        loc = p['location']
    if valid and len(sched) > max_count or (len(sched) == max_count and time < best_time):
        max_count = len(sched)
        best = sched
        best_time = time if len(sched) else 0

itinerary = []
for meet in best:
    itinerary.append({
        "action": "meet",
        "location": meet['l'],
        "person": meet['n'],
        "start_time": time_to_str(meet['s']),
        "end_time": time_to_str(meet['e'])
    })

print(json.dumps({"itinerary": itinerary}, indent=2))