import itertools
import json

friends = [
    {'name': 'Rebecca', 'location': 'Mission District', 'start': 690, 'end': 1215, 'duration': 120},
    {'name': 'Karen', 'location': 'Bayview', 'start': 765, 'end': 900, 'duration': 120},
    {'name': 'Carol', 'location': 'Sunset District', 'start': 615, 'end': 705, 'duration': 30}
]

travel_times = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Sunset District'): 26,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Sunset District'): 23,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Bayview'): 22,
}

def min_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

best = []
max_friends = 0

for perm in itertools.permutations(friends):
    schedule = []
    ct = 540  # 9:00 AM
    cl = 'Union Square'
    valid = True
    for f in perm:
        key = (cl, f['location'])
        if key not in travel_times:
            valid = False
            break
        arrive = ct + travel_times[key]
        start = max(arrive, f['start'])
        if start + f['duration'] > f['end']:
            valid = False
            break
        schedule.append((f, start, start + f['duration']))
        ct = start + f['duration']
        cl = f['location']
    if valid:
        if len(perm) > max_friends or (len(perm) == max_friends and sum(f['duration'] for f in perm) > sum(b[0]['duration'] for b in best)):
            max_friends = len(perm)
            best = schedule

itinerary = []
for entry in best:
    f, s, e = entry
    itinerary.append({
        "action": "meet",
        "location": f['location'],
        "person": f['name'],
        "start_time": min_to_time(s),
        "end_time": min_to_time(e)
    })

print(json.dumps({"itinerary": itinerary}, indent=2))