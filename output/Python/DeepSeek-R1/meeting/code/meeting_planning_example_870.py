import json

def mins_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

friends = [
    {
        'name': 'Linda',
        'location': 'Marina District',
        'start': 18 * 60,
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
        'name': 'Kimberly',
        'location': 'Richmond District',
        'start': 14 * 60 + 15,
        'end': 22 * 60,
        'duration': 30
    },
    {
        'name': 'Paul',
        'location': 'Alamo Square',
        'start': 21 * 60,
        'end': 21 * 60 + 30,
        'duration': 15
    },
    {
        'name': 'Carol',
        'location': 'Financial District',
        'start': 10 * 60 + 15,
        'end': 12 * 60,
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
        'name': 'Laura',
        'location': 'Mission District',
        'start': 16 * 60 + 15,
        'end': 20 * 60 + 30,
        'duration': 30
    },
    {
        'name': 'Sandra',
        'location': 'Nob Hill',
        'start': 9 * 60 + 15,
        'end': 18 * 60 + 30,
        'duration': 60
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'start': 18 * 60 + 30,
        'end': 22 * 60,
        'duration': 75
    }
]

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
        'Russian Hill': 7
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
        'Russian Hill': 8
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
        'Russian Hill': 18
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
        'Russian Hill': 13
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
        'Russian Hill': 13
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
        'Russian Hill': 11
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
        'Russian Hill': 14
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
        'Russian Hill': 15
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
        'Russian Hill': 5
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
        'Nob Hill': 5
    }
}

current_time = 540  # 9:00 AM
current_location = 'Pacific Heights'
itinerary = []
remaining_friends = friends.copy()

while remaining_friends:
    best_friend = None
    best_end = float('inf')
    best_start = None

    for friend in remaining_friends:
        travel_time = travel_times.get(current_location, {}).get(friend['location'], float('inf'))
        if travel_time == float('inf'):
            continue

        arrival_time = current_time + travel_time
        start_time = max(arrival_time, friend['start'])
        end_time = start_time + friend['duration']

        if end_time > friend['end']:
            continue

        if end_time < best_end:
            best_end = end_time
            best_friend = friend
            best_start = start_time

    if not best_friend:
        break

    itinerary.append({
        'action': 'meet',
        'location': best_friend['location'],
        'person': best_friend['name'],
        'start_time': mins_to_time(best_start),
        'end_time': mins_to_time(best_end)
    })
    current_time = best_end
    current_location = best_friend['location']
    remaining_friends.remove(best_friend)

output = {'itinerary': itinerary}
print(json.dumps(output, indent=2))