import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
travel_times = {
    'Marina District': {
        'Bayview': 27, 'Sunset District': 19, 'Richmond District': 11, 'Nob Hill': 12,
        'Chinatown': 15, 'Haight-Ashbury': 16, 'North Beach': 11, 'Russian Hill': 8, 'Embarcadero': 14
    },
    'Bayview': {
        'Marina District': 27, 'Sunset District': 23, 'Richmond District': 25, 'Nob Hill': 20,
        'Chinatown': 19, 'Haight-Ashbury': 19, 'North Beach': 22, 'Russian Hill': 23, 'Embarcadero': 19
    },
    'Sunset District': {
        'Marina District': 21, 'Bayview': 22, 'Richmond District': 12, 'Nob Hill': 27,
        'Chinatown': 30, 'Haight-Ashbury': 15, 'North Beach': 28, 'Russian Hill': 24, 'Embarcadero': 30
    },
    'Richmond District': {
        'Marina District': 9, 'Bayview': 27, 'Sunset District': 11, 'Nob Hill': 17,
        'Chinatown': 20, 'Haight-Ashbury': 10, 'North Beach': 17, 'Russian Hill': 13, 'Embarcadero': 19
    },
    'Nob Hill': {
        'Marina District': 11, 'Bayview': 19, 'Sunset District': 24, 'Richmond District': 14,
        'Chinatown': 6, 'Haight-Ashbury': 13, 'North Beach': 8, 'Russian Hill': 5, 'Embarcadero': 9
    },
    'Chinatown': {
        'Marina District': 12, 'Bayview': 20, 'Sunset District': 29, 'Richmond District': 20,
        'Nob Hill': 9, 'Haight-Ashbury': 19, 'North Beach': 3, 'Russian Hill': 7, 'Embarcadero': 5
    },
    'Haight-Ashbury': {
        'Marina District': 17, 'Bayview': 18, 'Sunset District': 15, 'Richmond District': 10,
        'Nob Hill': 15, 'Chinatown': 19, 'North Beach': 19, 'Russian Hill': 17, 'Embarcadero': 20
    },
    'North Beach': {
        'Marina District': 9, 'Bayview': 25, 'Sunset District': 27, 'Richmond District': 18,
        'Nob Hill': 7, 'Chinatown': 6, 'Haight-Ashbury': 18, 'Russian Hill': 4, 'Embarcadero': 6
    },
    'Russian Hill': {
        'Marina District': 7, 'Bayview': 23, 'Sunset District': 23, 'Richmond District': 14,
        'Nob Hill': 5, 'Chinatown': 9, 'Haight-Ashbury': 17, 'North Beach': 5, 'Embarcadero': 8
    },
    'Embarcadero': {
        'Marina District': 12, 'Bayview': 21, 'Sunset District': 30, 'Richmond District': 21,
        'Nob Hill': 10, 'Chinatown': 7, 'Haight-Ashbury': 21, 'North Beach': 5, 'Russian Hill': 8
    }
}

friends = [
    {'name': 'Charles', 'location': 'Bayview', 'start': '11:30', 'end': '14:30', 'duration': 45},
    {'name': 'Robert', 'location': 'Sunset District', 'start': '16:45', 'end': '21:00', 'duration': 30},
    {'name': 'Karen', 'location': 'Richmond District', 'start': '19:15', 'end': '21:30', 'duration': 60},
    {'name': 'Rebecca', 'location': 'Nob Hill', 'start': '16:15', 'end': '20:30', 'duration': 90},
    {'name': 'Margaret', 'location': 'Chinatown', 'start': '14:15', 'end': '19:45', 'duration': 120},
    {'name': 'Patricia', 'location': 'Haight-Ashbury', 'start': '14:30', 'end': '20:30', 'duration': 45},
    {'name': 'Mark', 'location': 'North Beach', 'start': '14:00', 'end': '18:30', 'duration': 105},
    {'name': 'Melissa', 'location': 'Russian Hill', 'start': '13:00', 'end': '19:45', 'duration': 30},
    {'name': 'Laura', 'location': 'Embarcadero', 'start': '7:45', 'end': '13:15', 'duration': 105}
]

current_time = time_to_minutes('9:00')
current_location = 'Marina District'
itinerary = []

# First, meet Laura at Embarcadero (earliest)
travel_time = travel_times[current_location]['Embarcadero']
meet_start = max(time_to_minutes('7:45'), current_time + travel_time)
meet_end = meet_start + 105
if meet_end <= time_to_minutes('13:15'):
    itinerary.append({
        'action': 'meet',
        'location': 'Embarcadero',
        'person': 'Laura',
        'start_time': minutes_to_time(meet_start),
        'end_time': minutes_to_time(meet_end)
    })
    current_time = meet_end
    current_location = 'Embarcadero'

# Next, meet Charles at Bayview
travel_time = travel_times[current_location]['Bayview']
meet_start = max(time_to_minutes('11:30'), current_time + travel_time)
meet_end = meet_start + 45
if meet_end <= time_to_minutes('14:30'):
    itinerary.append({
        'action': 'meet',
        'location': 'Bayview',
        'person': 'Charles',
        'start_time': minutes_to_time(meet_start),
        'end_time': minutes_to_time(meet_end)
    })
    current_time = meet_end
    current_location = 'Bayview'

# Next, meet Melissa at Russian Hill
travel_time = travel_times[current_location]['Russian Hill']
meet_start = max(time_to_minutes('13:00'), current_time + travel_time)
meet_end = meet_start + 30
if meet_end <= time_to_minutes('19:45'):
    itinerary.append({
        'action': 'meet',
        'location': 'Russian Hill',
        'person': 'Melissa',
        'start_time': minutes_to_time(meet_start),
        'end_time': minutes_to_time(meet_end)
    })
    current_time = meet_end
    current_location = 'Russian Hill'

# Next, meet Margaret at Chinatown
travel_time = travel_times[current_location]['Chinatown']
meet_start = max(time_to_minutes('14:15'), current_time + travel_time)
meet_end = meet_start + 120
if meet_end <= time_to_minutes('19:45'):
    itinerary.append({
        'action': 'meet',
        'location': 'Chinatown',
        'person': 'Margaret',
        'start_time': minutes_to_time(meet_start),
        'end_time': minutes_to_time(meet_end)
    })
    current_time = meet_end
    current_location = 'Chinatown'

# Next, meet Rebecca at Nob Hill
travel_time = travel_times[current_location]['Nob Hill']
meet_start = max(time_to_minutes('16:15'), current_time + travel_time)
meet_end = meet_start + 90
if meet_end <= time_to_minutes('20:30'):
    itinerary.append({
        'action': 'meet',
        'location': 'Nob Hill',
        'person': 'Rebecca',
        'start_time': minutes_to_time(meet_start),
        'end_time': minutes_to_time(meet_end)
    })
    current_time = meet_end
    current_location = 'Nob Hill'

# Next, meet Robert at Sunset District
travel_time = travel_times[current_location]['Sunset District']
meet_start = max(time_to_minutes('16:45'), current_time + travel_time)
meet_end = meet_start + 30
if meet_end <= time_to_minutes('21:00'):
    itinerary.append({
        'action': 'meet',
        'location': 'Sunset District',
        'person': 'Robert',
        'start_time': minutes_to_time(meet_start),
        'end_time': minutes_to_time(meet_end)
    })
    current_time = meet_end
    current_location = 'Sunset District'

# Finally, meet Karen at Richmond District
travel_time = travel_times[current_location]['Richmond District']
meet_start = max(time_to_minutes('19:15'), current_time + travel_time)
meet_end = meet_start + 60
if meet_end <= time_to_minutes('21:30'):
    itinerary.append({
        'action': 'meet',
        'location': 'Richmond District',
        'person': 'Karen',
        'start_time': minutes_to_time(meet_start),
        'end_time': minutes_to_time(meet_end)
    })

print(json.dumps({'itinerary': itinerary}, indent=2))