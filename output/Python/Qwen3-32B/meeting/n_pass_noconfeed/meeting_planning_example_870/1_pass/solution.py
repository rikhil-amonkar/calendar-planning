import copy
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    'Pacific Heights': {
        'Marina District': 6,
        'The Castro': 16,
        'Richmond District': 12,
        'Alamo Square': 10,
        'Financial District': 13,
        'Presidio': 11,
        'Mission District': 15,
        'Nob Hill': 8,
        'Russian Hill': 7,
    },
    'Marina District': {
        'Pacific Heights': 7,
        'The Castro': 22,
        'Richmond District': 11,
        'Alamo Square': 15,
        'Financial District': 17,
        'Presidio': 10,
        'Mission District': 20,
        'Nob Hill': 12,
        'Russian Hill': 8,
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Marina District': 21,
        'Richmond District': 16,
        'Alamo Square': 8,
        'Financial District': 21,
        'Presidio': 20,
        'Mission District': 7,
        'Nob Hill': 16,
        'Russian Hill': 18,
    },
    'Richmond District': {
        'Pacific Heights': 10,
        'Marina District': 9,
        'The Castro': 16,
        'Alamo Square': 13,
        'Financial District': 22,
        'Presidio': 7,
        'Mission District': 20,
        'Nob Hill': 17,
        'Russian Hill': 13,
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'Marina District': 15,
        'The Castro': 8,
        'Richmond District': 11,
        'Financial District': 17,
        'Presidio': 17,
        'Mission District': 10,
        'Nob Hill': 11,
        'Russian Hill': 13,
    },
    'Financial District': {
        'Pacific Heights': 13,
        'Marina District': 15,
        'The Castro': 20,
        'Richmond District': 21,
        'Alamo Square': 17,
        'Presidio': 22,
        'Mission District': 17,
        'Nob Hill': 8,
        'Russian Hill': 11,
    },
    'Presidio': {
        'Pacific Heights': 11,
        'Marina District': 11,
        'The Castro': 21,
        'Richmond District': 7,
        'Alamo Square': 19,
        'Financial District': 23,
        'Mission District': 26,
        'Nob Hill': 18,
        'Russian Hill': 14,
    },
    'Mission District': {
        'Pacific Heights': 16,
        'Marina District': 19,
        'The Castro': 7,
        'Richmond District': 20,
        'Alamo Square': 11,
        'Financial District': 15,
        'Presidio': 25,
        'Nob Hill': 12,
        'Russian Hill': 15,
    },
    'Nob Hill': {
        'Pacific Heights': 8,
        'Marina District': 11,
        'The Castro': 17,
        'Richmond District': 14,
        'Alamo Square': 11,
        'Financial District': 9,
        'Presidio': 17,
        'Mission District': 13,
        'Russian Hill': 5,
    },
    'Russian Hill': {
        'Pacific Heights': 7,
        'Marina District': 7,
        'The Castro': 21,
        'Richmond District': 14,
        'Alamo Square': 15,
        'Financial District': 11,
        'Presidio': 14,
        'Mission District': 16,
        'Nob Hill': 5,
    },
}

friends = [
    {
        'name': 'Carol',
        'location': 'Financial District',
        'start': 10 * 60 + 15,
        'end': 12 * 60,
        'duration': 60
    },
    {
        'name': 'Sandra',
        'location': 'Nob Hill',
        'start': 9 * 60 + 15,
        'end': 18 * 60 + 30,
        'duration': 60
    },
    {
        'name': 'Brian',
        'location': 'Presidio',
        'start': 10 * 60,
        'end': 21 * 60 + 30,
        'duration': 75
    },
    {
        'name': 'Kimberly',
        'location': 'Richmond District',
        'start': 14 * 60 + 15,
        'end': 22 * 60,
        'duration': 30
    },
    {
        'name': 'Kenneth',
        'location': 'The Castro',
        'start': 14 * 60 + 45,
        'end': 16 * 60 + 15,
        'duration': 30
    },
    {
        'name': 'Laura',
        'location': 'Mission District',
        'start': 16 * 60 + 15,
        'end': 20 * 60 + 30,
        'duration': 30
    },
    {
        'name': 'Linda',
        'location': 'Marina District',
        'start': 18 * 60,
        'end': 22 * 60,
        'duration': 30
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'start': 18 * 60 + 30,
        'end': 22 * 60,
        'duration': 75
    },
    {
        'name': 'Paul',
        'location': 'Alamo Square',
        'start': 21 * 60,
        'end': 21 * 60 + 30,
        'duration': 15
    }
]

best_itinerary = []

def backtrack(current_location, current_time, visited, itinerary):
    global best_itinerary
    for i in range(len(friends)):
        if i in visited:
            continue
        friend = friends[i]
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        latest_start = friend['end'] - friend['duration']
        if arrival_time > latest_start:
            continue
        earliest_start = max(friend['start'], arrival_time)
        if earliest_start + friend['duration'] > friend['end']:
            continue
        new_time = earliest_start + friend['duration']
        new_location = friend['location']
        new_visited = visited.copy()
        new_visited.add(i)
        new_itinerary = copy.deepcopy(itinerary)
        new_itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(earliest_start),
            'end_time': minutes_to_time(new_time),
        })
        if len(new_itinerary) > len(best_itinerary):
            best_itinerary = new_itinerary.copy()
        backtrack(new_location, new_time, new_visited, new_itinerary)

backtrack('Pacific Heights', 540, set(), [])

print(json.dumps({"itinerary": best_itinerary}))