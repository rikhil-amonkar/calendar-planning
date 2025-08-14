import json
from datetime import datetime

def time_to_minutes(time_str):
    dt = datetime.strptime(time_str, "%I:%M%p")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Mark',
        'location': "Fisherman's Wharf",
        'available_start': time_to_minutes("8:15AM"),
        'available_end': time_to_minutes("10:00AM"),
        'required_duration': 30
    },
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'available_start': time_to_minutes("12:15PM"),
        'available_end': time_to_minutes("3:00PM"),
        'required_duration': 75
    },
    {
        'name': 'Betty',
        'location': 'Bayview',
        'available_start': time_to_minutes("7:15AM"),
        'available_end': time_to_minutes("8:30PM"),
        'required_duration': 15
    },
    {
        'name': 'Lisa',
        'location': 'Haight-Ashbury',
        'available_start': time_to_minutes("3:30PM"),
        'available_end': time_to_minutes("6:30PM"),
        'required_duration': 45
    },
    {
        'name': 'William',
        'location': 'Russian Hill',
        'available_start': time_to_minutes("6:45PM"),
        'available_end': time_to_minutes("8:00PM"),
        'required_duration': 60
    },
    {
        'name': 'Brian',
        'location': 'The Castro',
        'available_start': time_to_minutes("9:15AM"),
        'available_end': time_to_minutes("1:15PM"),
        'required_duration': 30
    },
    {
        'name': 'Joseph',
        'location': 'Marina District',
        'available_start': time_to_minutes("10:45AM"),
        'available_end': time_to_minutes("3:00PM"),
        'required_duration': 90
    },
    {
        'name': 'Ashley',
        'location': 'Richmond District',
        'available_start': time_to_minutes("9:45AM"),
        'available_end': time_to_minutes("11:15AM"),
        'required_duration': 45
    },
    {
        'name': 'Patricia',
        'location': 'Union Square',
        'available_start': time_to_minutes("4:30PM"),
        'available_end': time_to_minutes("8:00PM"),
        'required_duration': 120
    },
    {
        'name': 'Karen',
        'location': 'Sunset District',
        'available_start': time_to_minutes("4:30PM"),
        'available_end': time_to_minutes("10:00PM"),
        'required_duration': 105
    }
]

travel_times = {
    'Financial District': {
        "Fisherman's Wharf": 10,
        'Presidio': 22,
        'Bayview': 19,
        'Haight-Ashbury': 19,
        'Russian Hill': 11,
        'The Castro': 20,
        'Marina District': 15,
        'Richmond District': 21,
        'Union Square': 9,
        'Sunset District': 30
    },
    "Fisherman's Wharf": {
        'Financial District': 11,
        'Presidio': 17,
        'Bayview': 26,
        'Haight-Ashbury': 22,
        'Russian Hill': 7,
        'The Castro': 27,
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 13,
        'Sunset District': 27
    },
    'Presidio': {
        'Financial District': 23,
        "Fisherman's Wharf": 19,
        'Bayview': 31,
        'Haight-Ashbury': 15,
        'Russian Hill': 14,
        'The Castro': 21,
        'Marina District': 11,
        'Richmond District': 7,
        'Union Square': 22,
        'Sunset District': 15
    },
    'Bayview': {
        'Financial District': 19,
        "Fisherman's Wharf": 25,
        'Presidio': 32,
        'Haight-Ashbury': 19,
        'Russian Hill': 23,
        'The Castro': 19,
        'Marina District': 27,
        'Richmond District': 25,
        'Union Square': 18,
        'Sunset District': 23
    },
    'Haight-Ashbury': {
        'Financial District': 21,
        "Fisherman's Wharf": 23,
        'Presidio': 15,
        'Bayview': 18,
        'Russian Hill': 17,
        'The Castro': 6,
        'Marina District': 17,
        'Richmond District': 10,
        'Union Square': 19,
        'Sunset District': 15
    },
    'Russian Hill': {
        'Financial District': 11,
        "Fisherman's Wharf": 7,
        'Presidio': 14,
        'Bayview': 23,
        'Haight-Ashbury': 17,
        'The Castro': 21,
        'Marina District': 7,
        'Richmond District': 14,
        'Union Square': 10,
        'Sunset District': 23
    },
    'The Castro': {
        'Financial District': 21,
        "Fisherman's Wharf": 24,
        'Presidio': 20,
        'Bayview': 19,
        'Haight-Ashbury': 6,
        'Russian Hill': 18,
        'Marina District': 21,
        'Richmond District': 16,
        'Union Square': 19,
        'Sunset District': 17
    },
    'Marina District': {
        'Financial District': 17,
        "Fisherman's Wharf": 10,
        'Presidio': 10,
        'Bayview': 27,
        'Haight-Ashbury': 16,
        'Russian Hill': 8,
        'The Castro': 22,
        'Richmond District': 11,
        'Union Square': 16,
        'Sunset District': 19
    },
    'Richmond District': {
        'Financial District': 22,
        "Fisherman's Wharf": 18,
        'Presidio': 7,
        'Bayview': 27,
        'Haight-Ashbury': 10,
        'Russian Hill': 13,
        'The Castro': 16,
        'Marina District': 9,
        'Union Square': 21,
        'Sunset District': 11
    },
    'Union Square': {
        'Financial District': 9,
        "Fisherman's Wharf": 15,
        'Presidio': 24,
        'Bayview': 15,
        'Haight-Ashbury': 18,
        'Russian Hill': 13,
        'The Castro': 17,
        'Marina District': 18,
        'Richmond District': 20,
        'Sunset District': 27
    },
    'Sunset District': {
        'Financial District': 30,
        "Fisherman's Wharf": 29,
        'Presidio': 16,
        'Bayview': 22,
        'Haight-Ashbury': 15,
        'Russian Hill': 24,
        'The Castro': 17,
        'Marina District': 21,
        'Richmond District': 12,
        'Union Square': 30
    }
}

best_itinerary = []

def explore(current_time, current_location, visited_mask, current_path):
    global best_itinerary

    if len(current_path) <= len(best_itinerary):
        unvisited_count = 10 - bin(visited_mask).count('1')
        upper_bound = len(current_path) + unvisited_count
        if upper_bound <= len(best_itinerary):
            return

    unvisited_friends = []
    for i in range(10):
        if not (visited_mask & (1 << i)):
            friend = friends[i]
            unvisited_friends.append((friend['available_start'], i))
    unvisited_friends.sort()
    for _, i in unvisited_friends:
        friend = friends[i]
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        start_time = max(friend['available_start'], arrival_time)
        end_time = start_time + friend['required_duration']
        if end_time > friend['available_end']:
            continue
        new_path = current_path + [{
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        }]
        if len(new_path) > len(best_itinerary):
            best_itinerary = new_path.copy()
        new_mask = visited_mask | (1 << i)
        explore(end_time, friend['location'], new_mask, new_path)

explore(540, 'Financial District', 0, [])

result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))