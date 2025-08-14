import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Richmond District': {
        'Marina District': 9,
        'Chinatown': 20,
        'Financial District': 22,
        'Bayview': 26,
        'Union Square': 21
    },
    'Marina District': {
        'Richmond District': 11,
        'Chinatown': 16,
        'Financial District': 17,
        'Bayview': 27,
        'Union Square': 16
    },
    'Chinatown': {
        'Richmond District': 20,
        'Marina District': 12,
        'Financial District': 5,
        'Bayview': 22,
        'Union Square': 7
    },
    'Financial District': {
        'Richmond District': 21,
        'Marina District': 15,
        'Chinatown': 5,
        'Bayview': 19,
        'Union Square': 9
    },
    'Bayview': {
        'Richmond District': 25,
        'Marina District': 25,
        'Chinatown': 18,
        'Financial District': 19,
        'Union Square': 17
    },
    'Union Square': {
        'Richmond District': 20,
        'Marina District': 18,
        'Chinatown': 7,
        'Financial District': 9,
        'Bayview': 15
    }
}

friends = [
    {
        'name': 'Margaret',
        'location': 'Bayview',
        'available_start': '9:30',
        'available_end': '13:30',
        'required_duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'available_start': '12:15',
        'available_end': '20:15',
        'required_duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'Marina District',
        'available_start': '13:15',
        'available_end': '16:45',
        'required_duration': 15
    },
    {
        'name': 'Rebecca',
        'location': 'Financial District',
        'available_start': '13:15',
        'available_end': '16:45',
        'required_duration': 75
    },
    {
        'name': 'Kenneth',
        'location': 'Union Square',
        'available_start': '19:30',
        'available_end': '21:15',
        'required_duration': 75
    }
]

def is_feasible(perm):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Richmond District'
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        available_start = time_str_to_minutes(friend['available_start'])
        available_end = time_str_to_minutes(friend['available_end'])
        required_duration = friend['required_duration']
        meeting_start = max(arrival_time, available_start)
        if meeting_start + required_duration > available_end:
            return False
        current_time = meeting_start + required_duration
        current_location = friend['location']
    return True

def build_itinerary(perm):
    itinerary = []
    current_time = 9 * 60
    current_location = 'Richmond District'
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        available_start = time_str_to_minutes(friend['available_start'])
        required_duration = friend['required_duration']
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + required_duration
        start_str = minutes_to_time_str(meeting_start)
        end_str = minutes_to_time_str(meeting_end)
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': start_str,
            'end_time': end_str
        })
        current_time = meeting_end
        current_location = friend['location']
    return itinerary

def find_optimal_schedule():
    for subset_size in range(len(friends), 0, -1):
        for subset in itertools.combinations(friends, subset_size):
            for perm in itertools.permutations(subset):
                if is_feasible(perm):
                    return {'itinerary': build_itinerary(perm)}
    return {'itinerary': []}  # if no feasible schedule found

if __name__ == '__main__':
    schedule = find_optimal_schedule()
    print(json.dumps(schedule, indent=2))