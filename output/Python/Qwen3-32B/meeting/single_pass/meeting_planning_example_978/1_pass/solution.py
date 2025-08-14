import json
from copy import deepcopy

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def find_optimal_sequence(current_time, current_location, friends_left):
    if not friends_left:
        return 0, []
    max_count = 0
    best_sequence = []
    for i in range(len(friends_left)):
        friend = friends_left[i]
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, friend['start_time'])
        meeting_end = meeting_start + friend['required_duration']
        if meeting_end > friend['end_time']:
            continue
        remaining_friends = friends_left[:i] + friends_left[i+1:]
        count, sequence = find_optimal_sequence(meeting_end, friend['location'], remaining_friends)
        count += 1
        meeting_entry = {
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        }
        new_sequence = [meeting_entry] + sequence
        if count > max_count:
            max_count = count
            best_sequence = new_sequence
    return max_count, best_sequence

travel_times = {
    'Embarcadero': {
        'Fisherman\'s Wharf': 6,
        'Financial District': 5,
        'Russian Hill': 8,
        'Marina District': 12,
        'Richmond District': 21,
        'Pacific Heights': 11,
        'Haight-Ashbury': 21,
        'Presidio': 20,
        'Nob Hill': 10,
        'The Castro': 25
    },
    'Fisherman\'s Wharf': {
        'Embarcadero': 8,
        'Financial District': 11,
        'Russian Hill': 7,
        'Marina District': 9,
        'Richmond District': 18,
        'Pacific Heights': 12,
        'Haight-Ashbury': 22,
        'Presidio': 17,
        'Nob Hill': 11,
        'The Castro': 27
    },
    'Financial District': {
        'Embarcadero': 4,
        'Fisherman\'s Wharf': 10,
        'Russian Hill': 11,
        'Marina District': 15,
        'Richmond District': 21,
        'Pacific Heights': 13,
        'Haight-Ashbury': 19,
        'Presidio': 22,
        'Nob Hill': 8,
        'The Castro': 20
    },
    'Russian Hill': {
        'Embarcadero': 8,
        'Fisherman\'s Wharf': 7,
        'Financial District': 11,
        'Marina District': 7,
        'Richmond District': 14,
        'Pacific Heights': 7,
        'Haight-Ashbury': 17,
        'Presidio': 14,
        'Nob Hill': 5,
        'The Castro': 21
    },
    'Marina District': {
        'Embarcadero': 14,
        'Fisherman\'s Wharf': 10,
        'Financial District': 17,
        'Russian Hill': 8,
        'Richmond District': 11,
        'Pacific Heights': 7,
        'Haight-Ashbury': 16,
        'Presidio': 10,
        'Nob Hill': 12,
        'The Castro': 22
    },
    'Richmond District': {
        'Embarcadero': 19,
        'Fisherman\'s Wharf': 18,
        'Financial District': 22,
        'Russian Hill': 13,
        'Marina District': 9,
        'Pacific Heights': 10,
        'Haight-Ashbury': 10,
        'Presidio': 7,
        'Nob Hill': 17,
        'The Castro': 16
    },
    'Pacific Heights': {
        'Embarcadero': 10,
        'Fisherman\'s Wharf': 13,
        'Financial District': 13,
        'Russian Hill': 7,
        'Marina District': 6,
        'Richmond District': 12,
        'Haight-Ashbury': 11,
        'Presidio': 11,
        'Nob Hill': 8,
        'The Castro': 16
    },
    'Haight-Ashbury': {
        'Embarcadero': 20,
        'Fisherman\'s Wharf': 23,
        'Financial District': 21,
        'Russian Hill': 17,
        'Marina District': 17,
        'Richmond District': 10,
        'Pacific Heights': 12,
        'Presidio': 15,
        'Nob Hill': 15,
        'The Castro': 6
    },
    'Presidio': {
        'Embarcadero': 20,
        'Fisherman\'s Wharf': 19,
        'Financial District': 23,
        'Russian Hill': 14,
        'Marina District': 11,
        'Richmond District': 7,
        'Pacific Heights': 11,
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'The Castro': 21
    },
    'Nob Hill': {
        'Embarcadero': 9,
        'Fisherman\'s Wharf': 10,
        'Financial District': 9,
        'Russian Hill': 5,
        'Marina District': 11,
        'Richmond District': 14,
        'Pacific Heights': 8,
        'Haight-Ashbury': 13,
        'Presidio': 17,
        'The Castro': 16
    },
    'The Castro': {
        'Embarcadero': 22,
        'Fisherman\'s Wharf': 24,
        'Financial District': 21,
        'Russian Hill': 18,
        'Marina District': 21,
        'Richmond District': 16,
        'Pacific Heights': 16,
        'Haight-Ashbury': 6,
        'Presidio': 20,
        'Nob Hill': 16
    }
}

friends = [
    {
        'name': 'Joseph',
        'location': 'Presidio',
        'start_time': 420,
        'end_time': 780,
        'required_duration': 45
    },
    {
        'name': 'Joshua',
        'location': 'Haight-Ashbury',
        'start_time': 540,
        'end_time': 930,
        'required_duration': 15
    },
    {
        'name': 'Betty',
        'location': 'Marina District',
        'start_time': 645,
        'end_time': 795,
        'required_duration': 60
    },
    {
        'name': 'Lisa',
        'location': 'Financial District',
        'start_time': 645,
        'end_time': 1035,
        'required_duration': 15
    },
    {
        'name': 'John',
        'location': 'The Castro',
        'start_time': 795,
        'end_time': 1185,
        'required_duration': 45
    },
    {
        'name': 'Stephanie',
        'location': 'Fisherman\'s Wharf',
        'start_time': 930,
        'end_time': 1320,
        'required_duration': 30
    },
    {
        'name': 'Melissa',
        'location': 'Russian Hill',
        'start_time': 1020,
        'end_time': 1245,
        'required_duration': 120
    },
    {
        'name': 'Sarah',
        'location': 'Richmond District',
        'start_time': 975,
        'end_time': 1170,
        'required_duration': 105
    },
    {
        'name': 'Daniel',
        'location': 'Pacific Heights',
        'start_time': 1110,
        'end_time': 1245,
        'required_duration': 60
    },
    {
        'name': 'Andrew',
        'location': 'Nob Hill',
        'start_time': 1185,
        'end_time': 1320,
        'required_duration': 105
    }
]

current_time = 540
current_location = 'Embarcadero'
max_count, best_sequence = find_optimal_sequence(current_time, current_location, friends)

result = {
    "itinerary": best_sequence
}
print(json.dumps(result, indent=2))