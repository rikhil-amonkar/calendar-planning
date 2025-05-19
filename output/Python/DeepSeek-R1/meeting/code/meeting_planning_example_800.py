import json

friends = [
    {
        'name': 'Melissa',
        'location': 'The Castro',
        'start': 20*60 +15,
        'end': 21*60 +15,
        'duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'North Beach',
        'start': 7*60,
        'end': 10*60 +30,
        'duration': 15
    },
    {
        'name': 'Joseph',
        'location': 'Embarcadero',
        'start': 15*60 +30,
        'end': 19*60 +30,
        'duration': 75
    },
    {
        'name': 'Barbara',
        'location': 'Alamo Square',
        'start': 20*60 +45,
        'end': 21*60 +45,
        'duration': 15
    },
    {
        'name': 'Kenneth',
        'location': 'Nob Hill',
        'start': 12*60 +15,
        'end': 17*60 +15,
        'duration': 105
    },
    {
        'name': 'Joshua',
        'location': 'Presidio',
        'start': 16*60 +30,
        'end': 18*60 +15,
        'duration': 105
    },
    {
        'name': 'Brian',
        'location': 'Fisherman\'s Wharf',
        'start': 9*60 +30,
        'end': 15*60 +30,
        'duration': 45
    },
    {
        'name': 'Steven',
        'location': 'Mission District',
        'start': 19*60 +30,
        'end': 21*60,
        'duration': 90
    },
    {
        'name': 'Betty',
        'location': 'Haight-Ashbury',
        'start': 19*60,
        'end': 20*60 +30,
        'duration': 90
    }
]

travel_times = {
    'Union Square': {'The Castro':17, 'North Beach':10, 'Embarcadero':11, 'Alamo Square':15, 'Nob Hill':9, 'Presidio':24, 'Fisherman\'s Wharf':15, 'Mission District':14, 'Haight-Ashbury':18},
    'The Castro': {'Union Square':19, 'North Beach':20, 'Embarcadero':22, 'Alamo Square':8, 'Nob Hill':16, 'Presidio':20, 'Fisherman\'s Wharf':24, 'Mission District':7, 'Haight-Ashbury':6},
    'North Beach': {'Union Square':7, 'The Castro':23, 'Embarcadero':6, 'Alamo Square':16, 'Nob Hill':7, 'Presidio':17, 'Fisherman\'s Wharf':5, 'Mission District':18, 'Haight-Ashbury':18},
    'Embarcadero': {'Union Square':10, 'The Castro':25, 'North Beach':5, 'Alamo Square':19, 'Nob Hill':10, 'Presidio':20, 'Fisherman\'s Wharf':6, 'Mission District':20, 'Haight-Ashbury':21},
    'Alamo Square': {'Union Square':14, 'The Castro':8, 'North Beach':15, 'Embarcadero':16, 'Nob Hill':11, 'Presidio':17, 'Fisherman\'s Wharf':19, 'Mission District':10, 'Haight-Ashbury':5},
    'Nob Hill': {'Union Square':7, 'The Castro':17, 'North Beach':8, 'Embarcadero':9, 'Alamo Square':11, 'Presidio':17, 'Fisherman\'s Wharf':10, 'Mission District':13, 'Haight-Ashbury':13},
    'Presidio': {'Union Square':22, 'The Castro':21, 'North Beach':18, 'Embarcadero':20, 'Alamo Square':19, 'Nob Hill':18, 'Fisherman\'s Wharf':19, 'Mission District':26, 'Haight-Ashbury':15},
    'Fisherman\'s Wharf': {'Union Square':13, 'The Castro':27, 'North Beach':6, 'Embarcadero':8, 'Alamo Square':21, 'Nob Hill':11, 'Presidio':17, 'Mission District':22, 'Haight-Ashbury':22},
    'Mission District': {'Union Square':15, 'The Castro':7, 'North Beach':17, 'Embarcadero':19, 'Alamo Square':11, 'Nob Hill':12, 'Presidio':25, 'Fisherman\'s Wharf':22, 'Haight-Ashbury':12},
    'Haight-Ashbury': {'Union Square':19, 'The Castro':6, 'North Beach':19, 'Embarcadero':20, 'Alamo Square':5, 'Nob Hill':15, 'Presidio':15, 'Fisherman\'s Wharf':23, 'Mission District':11},
}

current_time = 540  # 9:00 AM
current_location = 'Union Square'
itinerary = []
met = set()

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}" if m >=10 else f"{h}:0{m}"

while True:
    candidates = []
    for friend in friends:
        if friend['name'] in met:
            continue
        loc = friend['location']
        if current_location not in travel_times or loc not in travel_times[current_location]:
            continue
        travel_time = travel_times[current_location][loc]
        arrival = current_time + travel_time
        start = max(arrival, friend['start'])
        latest_start = friend['end'] - friend['duration']
        if start > latest_start:
            continue
        end = start + friend['duration']
        if end > friend['end']:
            continue
        candidates.append( (end, friend, start, end) )
    if not candidates:
        break
    candidates.sort()
    best = candidates[0]
    end_time, friend, start_time, end_time = best
    itinerary.append({
        'location': friend['location'],
        'person': friend['name'],
        'start_time': start_time,
        'end_time': end_time
    })
    current_time = end_time
    current_location = friend['location']
    met.add(friend['name'])

formatted = []
for item in itinerary:
    formatted.append({
        'action': 'meet',
        'location': item['location'],
        'person': item['person'],
        'start_time': format_time(item['start_time']).replace(':0', ':', 1) if item['start_time'] % 60 <10 else format_time(item['start_time']),
        'end_time': format_time(item['end_time']).replace(':0', ':', 1) if item['end_time'] % 60 <10 else format_time(item['end_time'])
    })

print(json.dumps({'itinerary': formatted}, indent=2))