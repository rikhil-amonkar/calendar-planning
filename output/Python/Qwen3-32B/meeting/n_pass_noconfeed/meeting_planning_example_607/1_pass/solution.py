import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def is_valid_schedule(perm, friends_data, travel_times):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Sunset District'
    itinerary = []

    for friend_name in perm:
        for friend in friends_data:
            if friend['name'] == friend_name:
                friend_data = friend
                break
        location = friend_data['location']
        available_start = time_str_to_minutes(friend_data['available_start'])
        available_end = time_str_to_minutes(friend_data['available_end'])
        required = friend_data['required_duration']

        travel_time = travel_times.get((current_location, location), float('inf'))
        arrival_time = current_time + travel_time

        earliest_start = max(arrival_time, available_start)
        latest_start = available_end - required

        if earliest_start > latest_start:
            return None

        meeting_end = earliest_start + required
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': friend_name,
            'start_time': minutes_to_time_str(earliest_start),
            'end_time': minutes_to_time_str(meeting_end)
        })

        current_time = meeting_end
        current_location = location

    return itinerary

friends = [
    {'name': 'Karen', 'location': 'Russian Hill', 'available_start': '20:45', 'available_end': '21:45', 'required_duration': 60},
    {'name': 'Jessica', 'location': 'The Castro', 'available_start': '15:45', 'available_end': '19:30', 'required_duration': 60},
    {'name': 'Matthew', 'location': 'Richmond District', 'available_start': '7:30', 'available_end': '15:15', 'required_duration': 15},
    {'name': 'Michelle', 'location': 'Marina District', 'available_start': '10:30', 'available_end': '18:45', 'required_duration': 75},
    {'name': 'Carol', 'location': 'North Beach', 'available_start': '12:00', 'available_end': '17:00', 'required_duration': 90},
    {'name': 'Stephanie', 'location': 'Union Square', 'available_start': '10:45', 'available_end': '14:15', 'required_duration': 30},
    {'name': 'Linda', 'location': 'Golden Gate Park', 'available_start': '10:45', 'available_end': '22:00', 'required_duration': 90},
]

travel_times = {
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Union Square'): 11,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Golden Gate Park'): 18,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Golden Gate Park'): 22,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Union Square'): 22,
}

all_friends = [f['name'] for f in friends]
best_itinerary = []
best_length = 0

for r in range(len(all_friends), 0, -1):
    for perm in itertools.permutations(all_friends, r):
        itinerary = is_valid_schedule(perm, friends, travel_times)
        if itinerary is not None:
            if len(itinerary) > best_length:
                best_length = len(itinerary)
                best_itinerary = itinerary
                if best_length == len(all_friends):
                    print(json.dumps({"itinerary": best_itinerary}, indent=2))
                    exit()

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))