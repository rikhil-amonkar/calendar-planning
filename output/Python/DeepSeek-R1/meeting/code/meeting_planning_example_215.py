import itertools
import json

def time_to_min(timestr):
    h, m = map(int, timestr.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    min = m % 60
    return f"{h}:{min:02d}"

travel_time = {
    'Bayview': {'Embarcadero': 19, 'Richmond District': 25, 'Fisherman\'s Wharf': 25},
    'Embarcadero': {'Bayview': 21, 'Richmond District': 21, 'Fisherman\'s Wharf': 6},
    'Richmond District': {'Bayview': 26, 'Embarcadero': 19, 'Fisherman\'s Wharf': 18},
    'Fisherman\'s Wharf': {'Bayview': 26, 'Embarcadero': 8, 'Richmond District': 18}
}

friends = [
    {'name': 'Jessica', 'location': 'Embarcadero', 'start': time_to_min('16:45'), 'end': time_to_min('19:00'), 'duration': 30},
    {'name': 'Sandra', 'location': 'Richmond District', 'start': time_to_min('18:30'), 'end': time_to_min('21:45'), 'duration': 120},
    {'name': 'Jason', 'location': 'Fisherman\'s Wharf', 'start': time_to_min('16:00'), 'end': time_to_min('16:45'), 'duration': 30}
]

best_itinerary = []
max_meetings = 0

for perm in itertools.permutations(friends):
    current_loc = 'Bayview'
    current_time = time_to_min('9:00')
    itinerary = []
    valid = True
    
    for f in perm:
        if current_loc not in travel_time or f['location'] not in travel_time[current_loc]:
            valid = False
            break
        travel = travel_time[current_loc][f['location']]
        arrival = current_time + travel
        start = max(arrival, f['start'])
        end = start + f['duration']
        if end > f['end']:
            valid = False
            break
        itinerary.append({
            'action': 'meet',
            'location': f['location'],
            'person': f['name'],
            'start_time': min_to_time(start),
            'end_time': min_to_time(end)
        })
        current_loc = f['location']
        current_time = end
    
    if valid and len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary

print(json.dumps({'itinerary': best_itinerary}, indent=2))