import itertools
import json

def time_to_min(timestr):
    hours, mins = map(int, timestr.split(':'))
    return hours * 60 + mins

friends = [
    {
        'name': 'Kevin',
        'location': 'Alamo Square',
        'start': time_to_min('8:15'),
        'end': time_to_min('21:30'),
        'duration': 75
    },
    {
        'name': 'Kimberly',
        'location': 'Russian Hill',
        'start': time_to_min('8:45'),
        'end': time_to_min('12:30'),
        'duration': 30
    },
    {
        'name': 'Joseph',
        'location': 'Presidio',
        'start': time_to_min('18:30'),
        'end': time_to_min('19:15'),
        'duration': 45
    },
    {
        'name': 'Thomas',
        'location': 'Financial District',
        'start': time_to_min('19:00'),
        'end': time_to_min('21:45'),
        'duration': 45
    }
]

travel_time = {
    'Sunset District': {'Alamo Square':17,'Russian Hill':24,'Presidio':16,'Financial District':30},
    'Alamo Square': {'Sunset District':16,'Russian Hill':13,'Presidio':18,'Financial District':17},
    'Russian Hill': {'Sunset District':23,'Alamo Square':15,'Presidio':14,'Financial District':11},
    'Presidio': {'Sunset District':15,'Alamo Square':18,'Russian Hill':14,'Financial District':23},
    'Financial District': {'Sunset District':31,'Alamo Square':17,'Russian Hill':10,'Presidio':22}
}

best_itinerary = []
max_met = 0
best_end = float('inf')

for perm in itertools.permutations(friends):
    current_loc = 'Sunset District'
    current_time = 540
    itinerary = []
    valid = True
    
    for f in perm:
        try:
            tt = travel_time[current_loc][f['location']]
        except KeyError:
            valid = False
            break
        arrive = current_time + tt
        earliest_start = max(arrive, f['start'])
        latest_start = f['end'] - f['duration']
        
        if earliest_start > latest_start:
            valid = False
            break
        
        end_time = earliest_start + f['duration']
        itinerary.append({
            'friend': f,
            'start': earliest_start,
            'end': end_time
        })
        current_time = end_time
        current_loc = f['location']
    
    if valid:
        num = len(itinerary)
        if num > max_met or (num == max_met and current_time < best_end):
            max_met = num
            best_itinerary = itinerary
            best_end = current_time

def min_to_time(m):
    return f"{m//60}:{m%60:02d}".replace(':0', ':') if m%60 ==0 else f"{m//60}:{m%60:02d}"

output = {"itinerary": []}
for item in best_itinerary:
    f = item['friend']
    output['itinerary'].append({
        "action": "meet",
        "location": f['location'],
        "person": f['name'],
        "start_time": min_to_time(item['start']),
        "end_time": min_to_time(item['end'])
    })

print(json.dumps(output, indent=2))