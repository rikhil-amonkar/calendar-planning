import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'The Castro': {
        'North Beach': 20,
        'Golden Gate Park': 11,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Richmond District': 16,
        'Nob Hill': 16,
        'Marina District': 21,
        'Presidio': 20,
        'Union Square': 19,
        'Financial District': 21
    },
    'North Beach': {
        'The Castro': 23,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Richmond District': 18,
        'Nob Hill': 7,
        'Marina District': 9,
        'Presidio': 17,
        'Union Square': 7,
        'Financial District': 8
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Richmond District': 7,
        'Nob Hill': 20,
        'Marina District': 16,
        'Presidio': 11,
        'Union Square': 22,
        'Financial District': 26
    },
    'Embarcadero': {
        'The Castro': 25,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Haight-Ashbury': 21,
        'Richmond District': 21,
        'Nob Hill': 10,
        'Marina District': 12,
        'Presidio': 20,
        'Union Square': 10,
        'Financial District': 5
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'North Beach': 19,
        'Golden Gate Park': 7,
        'Embarcadero': 20,
        'Richmond District': 10,
        'Nob Hill': 15,
        'Marina District': 17,
        'Presidio': 15,
        'Union Square': 19,
        'Financial District': 21
    },
    'Richmond District': {
        'The Castro': 16,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Nob Hill': 17,
        'Marina District': 9,
        'Presidio': 7,
        'Union Square': 21,
        'Financial District': 22
    },
    'Nob Hill': {
        'The Castro': 17,
        'North Beach': 8,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Haight-Ashbury': 13,
        'Richmond District': 14,
        'Marina District': 11,
        'Presidio': 17,
        'Union Square': 7,
        'Financial District': 9
    },
    'Marina District': {
        'The Castro': 22,
        'North Beach': 11,
        'Golden Gate Park': 18,
        'Embarcadero': 14,
        'Haight-Ashbury': 16,
        'Richmond District': 11,
        'Nob Hill': 12,
        'Presidio': 10,
        'Union Square': 16,
        'Financial District': 17
    },
    'Presidio': {
        'The Castro': 21,
        'North Beach': 18,
        'Golden Gate Park': 12,
        'Embarcadero': 20,
        'Haight-Ashbury': 15,
        'Richmond District': 7,
        'Nob Hill': 18,
        'Marina District': 11,
        'Union Square': 22,
        'Financial District': 23
    },
    'Union Square': {
        'The Castro': 17,
        'North Beach': 10,
        'Golden Gate Park': 22,
        'Embarcadero': 11,
        'Haight-Ashbury': 18,
        'Richmond District': 20,
        'Nob Hill': 9,
        'Marina District': 18,
        'Presidio': 24,
        'Financial District': 9
    },
    'Financial District': {
        'The Castro': 20,
        'North Beach': 7,
        'Golden Gate Park': 23,
        'Embarcadero': 4,
        'Haight-Ashbury': 19,
        'Richmond District': 21,
        'Nob Hill': 8,
        'Marina District': 15,
        'Presidio': 22,
        'Union Square': 9
    }
}

# Friend data: name, location, available_start, available_end, min_duration (minutes)
friends = [
    ('Steven', 'North Beach', 17.5, 20.5, 15),
    ('Sarah', 'Golden Gate Park', 17.0, 19.25, 75),
    ('Brian', 'Embarcadero', 14.25, 16.0, 105),
    ('Stephanie', 'Haight-Ashbury', 10.25, 12.25, 75),
    ('Melissa', 'Richmond District', 14.0, 19.5, 30),
    ('Nancy', 'Nob Hill', 8.25, 12.75, 90),
    ('David', 'Marina District', 11.25, 13.25, 120),
    ('James', 'Presidio', 15.0, 18.25, 120),
    ('Elizabeth', 'Union Square', 11.5, 21.0, 60),
    ('Robert', 'Financial District', 13.25, 15.25, 45)
]

def time_to_float(time_str):
    if isinstance(time_str, float):
        return time_str
    hours, minutes = map(float, time_str.split(':'))
    return hours + minutes / 60

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    try:
        return travel_times[from_loc][to_loc] / 60
    except KeyError:
        return travel_times[to_loc][from_loc] / 60

def can_schedule(prev_end, friend, current_location):
    travel_time = get_travel_time(current_location, friend[1])
    available_start = friend[2]
    available_end = friend[3]
    min_duration = friend[4] / 60
    
    start_time = max(prev_end + travel_time, available_start)
    end_time = start_time + min_duration
    
    if end_time > available_end:
        return None
    
    return (start_time, end_time)

def evaluate_schedule(order):
    current_time = 9.0  # Starting at The Castro at 9:00 AM
    current_location = 'The Castro'
    schedule = []
    met_friends = set()
    
    for friend in order:
        meeting = can_schedule(current_time, friend, current_location)
        if not meeting:
            continue
        
        start_time, end_time = meeting
        schedule.append({
            'action': 'meet',
            'location': friend[1],
            'person': friend[0],
            'start_time': float_to_time(start_time),
            'end_time': float_to_time(end_time)
        })
        met_friends.add(friend[0])
        current_time = end_time
        current_location = friend[1]
    
    # Try to meet Steven at the end if not already met
    steven = next(f for f in friends if f[0] == 'Steven')
    if 'Steven' not in met_friends:
        meeting = can_schedule(current_time, steven, current_location)
        if meeting:
            start_time, end_time = meeting
            schedule.append({
                'action': 'meet',
                'location': steven[1],
                'person': steven[0],
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
            met_friends.add('Steven')
    
    return len(met_friends), schedule

def find_optimal_schedule():
    # We'll try permutations of friends to find the best schedule
    # Since trying all permutations is too expensive, we'll try a subset
    best_count = 0
    best_schedule = []
    
    # Try different orders prioritizing friends with tighter time windows first
    sorted_friends = sorted(friends, key=lambda x: x[3] - x[2])
    
    # Try several permutations
    for _ in range(1000):
        import random
        random.shuffle(sorted_friends)
        count, schedule = evaluate_schedule(sorted_friends)
        if count > best_count or (count == best_count and len(schedule) > len(best_schedule)):
            best_count = count
            best_schedule = schedule
    
    return best_schedule

optimal_schedule = find_optimal_schedule()
output = {
    "itinerary": optimal_schedule
}

print(json.dumps(output, indent=2))