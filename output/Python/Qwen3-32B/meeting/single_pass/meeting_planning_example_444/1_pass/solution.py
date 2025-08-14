import itertools
import json

def time_str_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

travel_times = {
    'Financial District': {
        'Russian Hill': 10,
        'Sunset District': 31,
        'North Beach': 7,
        'The Castro': 23,
        'Golden Gate Park': 23
    },
    'Russian Hill': {
        'Financial District': 11,
        'Sunset District': 23,
        'North Beach': 5,
        'The Castro': 21,
        'Golden Gate Park': 21
    },
    'Sunset District': {
        'Financial District': 30,
        'Russian Hill': 24,
        'North Beach': 29,
        'The Castro': 17,
        'Golden Gate Park': 11
    },
    'North Beach': {
        'Financial District': 8,
        'Russian Hill': 4,
        'Sunset District': 27,
        'The Castro': 22,
        'Golden Gate Park': 22
    },
    'The Castro': {
        'Financial District': 20,
        'Russian Hill': 18,
        'Sunset District': 17,
        'North Beach': 20,
        'Golden Gate Park': 11
    },
    'Golden Gate Park': {
        'Financial District': 26,
        'Russian Hill': 19,
        'Sunset District': 10,
        'North Beach': 24,
        'The Castro': 13
    }
}

friends = [
    {
        'name': 'Ronald',
        'location': 'Russian Hill',
        'available_start': time_str_to_minutes('13:45'),
        'available_end': time_str_to_minutes('17:15'),
        'required_duration': 105
    },
    {
        'name': 'Patricia',
        'location': 'Sunset District',
        'available_start': time_str_to_minutes('9:15'),
        'available_end': time_str_to_minutes('22:00'),
        'required_duration': 60
    },
    {
        'name': 'Laura',
        'location': 'North Beach',
        'available_start': time_str_to_minutes('12:30'),
        'available_end': time_str_to_minutes('12:45'),
        'required_duration': 15
    },
    {
        'name': 'Emily',
        'location': 'The Castro',
        'available_start': time_str_to_minutes('16:15'),
        'available_end': time_str_to_minutes('18:30'),
        'required_duration': 60
    },
    {
        'name': 'Mary',
        'location': 'Golden Gate Park',
        'available_start': time_str_to_minutes('15:00'),
        'available_end': time_str_to_minutes('16:30'),
        'required_duration': 60
    }
]

best_itinerary = []
best_count = 0

for subset_size in range(1, len(friends) + 1):
    for combination in itertools.combinations(friends, subset_size):
        for permutation in itertools.permutations(combination):
            current_time = 9 * 60  # 9:00 AM in minutes
            current_location = 'Financial District'
            itinerary = []
            valid = True
            for friend in permutation:
                from_location = current_location
                to_location = friend['location']
                travel_time = travel_times[from_location][to_location]
                arrival_time = current_time + travel_time
                available_start = friend['available_start']
                available_end = friend['available_end']
                required = friend['required_duration']
                start_time = max(arrival_time, available_start)
                end_time = start_time + required
                if end_time > available_end:
                    valid = False
                    break
                itinerary.append({
                    'action': 'meet',
                    'location': to_location,
                    'person': friend['name'],
                    'start_time': minutes_to_time_str(start_time),
                    'end_time': minutes_to_time_str(end_time)
                })
                current_time = end_time
                current_location = to_location
            if valid:
                if len(itinerary) > best_count:
                    best_count = len(itinerary)
                    best_itinerary = itinerary
                elif len(itinerary) == best_count:
                    current_end = current_time
                    best_end = time_str_to_minutes(best_itinerary[-1]['end_time']) if best_itinerary else 0
                    if best_itinerary and current_end < best_end:
                        best_itinerary = itinerary

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))