import itertools
import json

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

friends_data = [
    {
        'name': 'Ronald',
        'location': 'Nob Hill',
        'available_start': 600,
        'available_end': 1020,
        'required': 105
    },
    {
        'name': 'Helen',
        'location': 'The Castro',
        'available_start': 810,
        'available_end': 1020,
        'required': 120
    },
    {
        'name': 'Joshua',
        'location': 'Sunset District',
        'available_start': 855,
        'available_end': 1170,
        'required': 90
    },
    {
        'name': 'Margaret',
        'location': 'Haight-Ashbury',
        'available_start': 615,
        'available_end': 1320,
        'required': 60
    }
]

locations_map = {
    'Pacific Heights': 0,
    'Nob Hill': 1,
    'Russian Hill': 2,
    'The Castro': 3,
    'Sunset District': 4,
    'Haight-Ashbury': 5
}

travel_times = [
    [0, 8, 7, 16, 21, 11],
    [8, 0, 5, 17, 25, 13],
    [7, 5, 0, 21, 23, 17],
    [16, 16, 18, 0, 17, 6],
    [21, 27, 24, 17, 0, 15],
    [12, 15, 17, 6, 15, 0],
]

def check_permutation(perm):
    current_time = 540  # 9:00 AM
    current_location = 0  # Pacific Heights
    meetings = []
    for idx in perm:
        friend = friends_data[idx]
        loc_name = friend['location']
        loc_code = locations_map[loc_name]
        travel_time = travel_times[current_location][loc_code]
        arrival_time = current_time + travel_time
        start_time = max(arrival_time, friend['available_start'])
        end_time = start_time + friend['required']
        if end_time > friend['available_end']:
            return None  # not feasible
        # Add to meetings
        meetings.append({
            'person': friend['name'],
            'start_time': start_time,
            'end_time': end_time
        })
        current_time = end_time
        current_location = loc_code
    return meetings

# Generate all subsets from largest to smallest
friends_indices = list(range(4))  # 0-3
for subset_size in range(4, 0, -1):
    for subset in itertools.combinations(friends_indices, subset_size):
        for perm in itertools.permutations(subset):
            meetings = check_permutation(perm)
            if meetings is not None:
                # Found a feasible permutation
                itinerary = []
                for m in meetings:
                    itinerary.append({
                        "action": "meet",
                        "person": m['person'],
                        "start_time": minutes_to_time_str(m['start_time']),
                        "end_time": minutes_to_time_str(m['end_time'])
                    })
                solution = {"itinerary": itinerary}
                print(json.dumps(solution, indent=2))
                exit()

# If no solution found for any subset
print(json.dumps({"itinerary": []}))