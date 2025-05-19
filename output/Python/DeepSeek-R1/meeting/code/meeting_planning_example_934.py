import json

def time_to_minutes(t):
    hours = int(t)
    minutes = int(round((t - hours) * 100))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'Nob Hill': {'Embarcadero':9, 'The Castro':17, 'Haight-Ashbury':13, 'Union Square':7, 'North Beach':8, 'Pacific Heights':8, 'Chinatown':6, 'Golden Gate Park':17, 'Marina District':11, 'Russian Hill':5},
    'Embarcadero': {'Nob Hill':10, 'The Castro':25, 'Haight-Ashbury':21, 'Union Square':10, 'North Beach':5, 'Pacific Heights':11, 'Chinatown':7, 'Golden Gate Park':25, 'Marina District':12, 'Russian Hill':8},
    'The Castro': {'Nob Hill':16, 'Embarcadero':22, 'Haight-Ashbury':6, 'Union Square':19, 'North Beach':20, 'Pacific Heights':16, 'Chinatown':22, 'Golden Gate Park':11, 'Marina District':21, 'Russian Hill':18},
    'Haight-Ashbury': {'Nob Hill':15, 'Embarcadero':20, 'The Castro':6, 'Union Square':19, 'North Beach':19, 'Pacific Heights':12, 'Chinatown':19, 'Golden Gate Park':7, 'Marina District':17, 'Russian Hill':17},
    'Union Square': {'Nob Hill':9, 'Embarcadero':11, 'The Castro':17, 'Haight-Ashbury':18, 'North Beach':10, 'Pacific Heights':15, 'Chinatown':7, 'Golden Gate Park':22, 'Marina District':18, 'Russian Hill':13},
    'North Beach': {'Nob Hill':7, 'Embarcadero':6, 'The Castro':23, 'Haight-Ashbury':18, 'Union Square':7, 'Pacific Heights':8, 'Chinatown':6, 'Golden Gate Park':22, 'Marina District':9, 'Russian Hill':4},
    'Pacific Heights': {'Nob Hill':8, 'Embarcadero':10, 'The Castro':16, 'Haight-Ashbury':11, 'Union Square':12, 'North Beach':9, 'Chinatown':11, 'Golden Gate Park':15, 'Marina District':6, 'Russian Hill':7},
    'Chinatown': {'Nob Hill':9, 'Embarcadero':5, 'The Castro':22, 'Haight-Ashbury':19, 'Union Square':7, 'North Beach':3, 'Pacific Heights':10, 'Golden Gate Park':23, 'Marina District':12, 'Russian Hill':7},
    'Golden Gate Park': {'Nob Hill':20, 'Embarcadero':25, 'The Castro':13, 'Haight-Ashbury':7, 'Union Square':22, 'North Beach':23, 'Pacific Heights':16, 'Chinatown':23, 'Marina District':16, 'Russian Hill':19},
    'Marina District': {'Nob Hill':12, 'Embarcadero':14, 'The Castro':22, 'Haight-Ashbury':16, 'Union Square':16, 'North Beach':11, 'Pacific Heights':7, 'Chinatown':15, 'Golden Gate Park':18, 'Russian Hill':8},
    'Russian Hill': {'Nob Hill':5, 'Embarcadero':8, 'The Castro':21, 'Haight-Ashbury':17, 'Union Square':10, 'North Beach':5, 'Pacific Heights':7, 'Chinatown':9, 'Golden Gate Park':21, 'Marina District':7}
}

friends = [
    {'name': 'Mary', 'location': 'Embarcadero', 'start': time_to_minutes(20.0), 'end': time_to_minutes(21.25), 'duration': 75},
    {'name': 'Joseph', 'location': 'Haight-Ashbury', 'start': time_to_minutes(20.0), 'end': time_to_minutes(22.0), 'duration': 120},
    {'name': 'David', 'location': 'Marina District', 'start': time_to_minutes(20.0), 'end': time_to_minutes(21.0), 'duration': 60},
    {'name': 'Thomas', 'location': 'North Beach', 'start': time_to_minutes(19.25), 'end': time_to_minutes(19.75), 'duration': 15},
    {'name': 'Mark', 'location': 'Golden Gate Park', 'start': time_to_minutes(17.5), 'end': time_to_minutes(21.5), 'duration': 120},
    {'name': 'Daniel', 'location': 'Pacific Heights', 'start': time_to_minutes(13.75), 'end': time_to_minutes(20.5), 'duration': 15},
    {'name': 'Karen', 'location': 'Russian Hill', 'start': time_to_minutes(13.25), 'end': time_to_minutes(18.5), 'duration': 120},
    {'name': 'Sarah', 'location': 'Union Square', 'start': time_to_minutes(11.75), 'end': time_to_minutes(14.5), 'duration': 90},
    {'name': 'Kenneth', 'location': 'The Castro', 'start': time_to_minutes(11.25), 'end': time_to_minutes(19.25), 'duration': 30},
    {'name': 'Richard', 'location': 'Chinatown', 'start': time_to_minutes(8.0), 'end': time_to_minutes(18.75), 'duration': 30}
]

friends.sort(key=lambda x: x['end'])

itinerary = []
current_location = 'Nob Hill'
current_time = 9 * 60  # 9:00 AM in minutes

for friend in friends:
    if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
        continue  # Skip if no travel time exists
    travel_duration = travel_times[current_location][friend['location']]
    arrival_time = current_time + travel_duration
    earliest_start = max(arrival_time, friend['start'])
    latest_start = friend['end'] - friend['duration']
    
    if earliest_start > latest_start:
        continue  # Can't meet this friend
    
    start_time = earliest_start
    end_time = start_time + friend['duration']
    
    if end_time > friend['end']:
        continue  # Doesn't fit
    
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    })
    
    current_time = end_time
    current_location = friend['location']

print(json.dumps({'itinerary': itinerary}, indent=2))