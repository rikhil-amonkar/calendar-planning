import json

friends = [
    {
        'name': 'Laura',
        'location': 'Alamo Square',
        'available_start': 14 * 60 + 30,  # 870
        'available_end': 16 * 60 + 15,    # 975
        'min_duration': 75
    },
    {
        'name': 'Brian',
        'location': 'Presidio',
        'available_start': 10 * 60 + 15,  # 615
        'available_end': 17 * 60,         # 1020
        'min_duration': 30
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'available_start': 18 * 60,       # 1080
        'available_end': 20 * 60 + 15,    # 1215
        'min_duration': 90
    },
    {
        'name': 'Stephanie',
        'location': 'North Beach',
        'available_start': 10 * 60 + 15,  # 615
        'available_end': 16 * 60,         # 960
        'min_duration': 75
    },
    {
        'name': 'Helen',
        'location': 'Golden Gate Park',
        'available_start': 11 * 60 + 30,  # 690
        'available_end': 21 * 60 + 45,    # 1305
        'min_duration': 120
    },
    {
        'name': 'Sandra',
        'location': 'Richmond District',
        'available_start': 8 * 60,        # 480
        'available_end': 15 * 60 + 15,    # 915
        'min_duration': 30
    },
    {
        'name': 'Mary',
        'location': 'Embarcadero',
        'available_start': 16 * 60 + 45,  # 1005
        'available_end': 18 * 60 + 45,    # 1125
        'min_duration': 120
    },
    {
        'name': 'Deborah',
        'location': 'Financial District',
        'available_start': 19 * 60,       # 1140
        'available_end': 20 * 60 + 45,    # 1245
        'min_duration': 105
    },
    {
        'name': 'Elizabeth',
        'location': 'Marina District',
        'available_start': 8 * 60 + 30,   # 510
        'available_end': 13 * 60 + 15,    # 795
        'min_duration': 105
    }
]

travel_time = {
    'Mission District': {
        'Alamo Square': 11,
        'Presidio': 25,
        'Russian Hill': 15,
        'North Beach': 17,
        'Golden Gate Park': 17,
        'Richmond District': 20,
        'Embarcadero': 19,
        'Financial District': 15,
        'Marina District': 19
    },
    'Alamo Square': {
        'Mission District': 10,
        'Presidio': 17,
        'Russian Hill': 13,
        'North Beach': 15,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Embarcadero': 16,
        'Financial District': 17,
        'Marina District': 15
    },
    'Presidio': {
        'Mission District': 26,
        'Alamo Square': 19,
        'Russian Hill': 14,
        'North Beach': 18,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Embarcadero': 20,
        'Financial District': 23,
        'Marina District': 11
    },
    'Russian Hill': {
        'Mission District': 16,
        'Alamo Square': 15,
        'Presidio': 14,
        'North Beach': 5,
        'Golden Gate Park': 21,
        'Richmond District': 14,
        'Embarcadero': 8,
        'Financial District': 11,
        'Marina District': 7
    },
    'North Beach': {
        'Mission District': 18,
        'Alamo Square': 16,
        'Presidio': 17,
        'Russian Hill': 4,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Embarcadero': 6,
        'Financial District': 8,
        'Marina District': 9
    },
    'Golden Gate Park': {
        'Mission District': 17,
        'Alamo Square': 9,
        'Presidio': 11,
        'Russian Hill': 19,
        'North Beach': 23,
        'Richmond District': 7,
        'Embarcadero': 25,
        'Financial District': 26,
        'Marina District': 16
    },
    'Richmond District': {
        'Mission District': 20,
        'Alamo Square': 13,
        'Presidio': 7,
        'Russian Hill': 13,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Financial District': 22,
        'Marina District': 9
    },
    'Embarcadero': {
        'Mission District': 20,
        'Alamo Square': 19,
        'Presidio': 20,
        'Russian Hill': 8,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Financial District': 5,
        'Marina District': 14
    },
    'Financial District': {
        'Mission District': 17,
        'Alamo Square': 17,
        'Presidio': 22,
        'Russian Hill': 11,
        'North Beach': 7,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Embarcadero': 4,
        'Marina District': 15
    },
    'Marina District': {
        'Mission District': 20,
        'Alamo Square': 15,
        'Presidio': 10,
        'Russian Hill': 8,
        'North Beach': 11,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Embarcadero': 14,
        'Financial District': 17
    }
}

best_sequence = []

def backtrack(current_sequence, current_time, current_location):
    global best_sequence
    if len(current_sequence) > len(best_sequence):
        best_sequence = list(current_sequence)
    for friend in friends:
        if friend not in current_sequence:
            travel_duration = travel_time[current_location][friend['location']]
            arrival_time = current_time + travel_duration
            start_time = max(arrival_time, friend['available_start'])
            end_time = start_time + friend['min_duration']
            if end_time <= friend['available_end']:
                current_sequence.append(friend)
                backtrack(current_sequence, end_time, friend['location'])
                current_sequence.pop()

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

backtrack([], 9 * 60, 'Mission District')

itinerary = []
current_time = 9 * 60
current_location = 'Mission District'

for friend in best_sequence:
    travel_duration = travel_time[current_location][friend['location']]
    arrival_time = current_time + travel_duration
    start_time = max(arrival_time, friend['available_start'])
    end_time = start_time + friend['min_duration']
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': format_time(start_time),
        'end_time': format_time(end_time)
    })
    current_time = end_time
    current_location = friend['location']

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))