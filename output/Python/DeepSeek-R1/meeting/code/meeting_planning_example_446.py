import itertools
import json

def time_to_minutes(timestr):
    time_part, period = timestr[:-2], timestr[-2:]
    hours, minutes = map(int, time_part.split(':'))
    if period == 'PM' and hours != 12:
        hours += 12
    if period == 'AM' and hours == 12:
        hours = 0
    return hours * 60 + minutes

friends = [
    {
        'name': 'Kimberly',
        'location': 'Marina District',
        'start': time_to_minutes('1:15PM'),
        'end': time_to_minutes('4:45PM'),
        'duration': 15
    },
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'start': time_to_minutes('12:15PM'),
        'end': time_to_minutes('8:15PM'),
        'duration': 15
    },
    {
        'name': 'Rebecca',
        'location': 'Financial District',
        'start': time_to_minutes('1:15PM'),
        'end': time_to_minutes('4:45PM'),
        'duration': 75
    },
    {
        'name': 'Margaret',
        'location': 'Bayview',
        'start': time_to_minutes('9:30AM'),
        'end': time_to_minutes('1:30PM'),
        'duration': 30
    },
    {
        'name': 'Kenneth',
        'location': 'Union Square',
        'start': time_to_minutes('7:30PM'),
        'end': time_to_minutes('9:15PM'),
        'duration': 75
    }
]

travel_times = {
    'Richmond District': {'Marina District':9, 'Chinatown':20, 'Financial District':22, 'Bayview':26, 'Union Square':21},
    'Marina District': {'Richmond District':11, 'Chinatown':16, 'Financial District':17, 'Bayview':27, 'Union Square':16},
    'Chinatown': {'Richmond District':20, 'Marina District':12, 'Financial District':5, 'Bayview':22, 'Union Square':7},
    'Financial District': {'Richmond District':21, 'Marina District':15, 'Chinatown':5, 'Bayview':19, 'Union Square':9},
    'Bayview': {'Richmond District':25, 'Marina District':25, 'Chinatown':18, 'Financial District':19, 'Union Square':17},
    'Union Square': {'Richmond District':20, 'Marina District':18, 'Chinatown':7, 'Financial District':9, 'Bayview':15}
}

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

best_schedule = []
max_met = 0
best_end_time = float('inf')

for perm in itertools.permutations(friends):
    current_location = 'Richmond District'
    current_time = 540
    schedule = []
    met = set()
    
    for friend in perm:
        if friend['name'] in met:
            continue
        if friend['location'] not in travel_times[current_location]:
            continue
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        start = max(arrival_time, friend['start'])
        end = start + friend['duration']
        if end > friend['end']:
            continue
        schedule.append({'friend': friend, 'start': start, 'end': end, 'location': friend['location']})
        met.add(friend['name'])
        current_time = end
        current_location = friend['location']
    
    if len(met) > max_met or (len(met) == max_met and current_time < best_end_time):
        max_met = len(met)
        best_schedule = schedule.copy()
        best_end_time = current_time

itinerary = []
for entry in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": entry['location'],
        "person": entry['friend']['name'],
        "start_time": minutes_to_time(entry['start']),
        "end_time": minutes_to_time(entry['end'])
    })

output = {"itinerary": sorted(itinerary, key=lambda x: x['start_time'])}

print(json.dumps(output, indent=2))