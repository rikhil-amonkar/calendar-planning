import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times dictionary: {from_location: {to_location: minutes}}
travel_times = {
    'Haight-Ashbury': {
        'Mission District': 11,
        'Union Square': 19,
        'Pacific Heights': 12,
        'Bayview': 18,
        'Fisherman\'s Wharf': 23,
        'Marina District': 17,
        'Richmond District': 10,
        'Sunset District': 15,
        'Golden Gate Park': 7
    },
    'Mission District': {
        'Haight-Ashbury': 12,
        'Union Square': 15,
        'Pacific Heights': 16,
        'Bayview': 14,
        'Fisherman\'s Wharf': 22,
        'Marina District': 19,
        'Richmond District': 20,
        'Sunset District': 24,
        'Golden Gate Park': 17
    },
    'Union Square': {
        'Haight-Ashbury': 18,
        'Mission District': 14,
        'Pacific Heights': 15,
        'Bayview': 15,
        'Fisherman\'s Wharf': 15,
        'Marina District': 18,
        'Richmond District': 20,
        'Sunset District': 27,
        'Golden Gate Park': 22
    },
    'Pacific Heights': {
        'Haight-Ashbury': 11,
        'Mission District': 15,
        'Union Square': 12,
        'Bayview': 22,
        'Fisherman\'s Wharf': 13,
        'Marina District': 6,
        'Richmond District': 12,
        'Sunset District': 21,
        'Golden Gate Park': 15
    },
    'Bayview': {
        'Haight-Ashbury': 19,
        'Mission District': 13,
        'Union Square': 18,
        'Pacific Heights': 23,
        'Fisherman\'s Wharf': 25,
        'Marina District': 27,
        'Richmond District': 25,
        'Sunset District': 23,
        'Golden Gate Park': 22
    },
    'Fisherman\'s Wharf': {
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Union Square': 13,
        'Pacific Heights': 12,
        'Bayview': 26,
        'Marina District': 9,
        'Richmond District': 18,
        'Sunset District': 27,
        'Golden Gate Park': 25
    },
    'Marina District': {
        'Haight-Ashbury': 16,
        'Mission District': 20,
        'Union Square': 16,
        'Pacific Heights': 7,
        'Bayview': 27,
        'Fisherman\'s Wharf': 10,
        'Richmond District': 11,
        'Sunset District': 19,
        'Golden Gate Park': 18
    },
    'Richmond District': {
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Union Square': 21,
        'Pacific Heights': 10,
        'Bayview': 27,
        'Fisherman\'s Wharf': 18,
        'Marina District': 9,
        'Sunset District': 11,
        'Golden Gate Park': 9
    },
    'Sunset District': {
        'Haight-Ashbury': 15,
        'Mission District': 25,
        'Union Square': 30,
        'Pacific Heights': 21,
        'Bayview': 22,
        'Fisherman\'s Wharf': 29,
        'Marina District': 21,
        'Richmond District': 12,
        'Golden Gate Park': 11
    },
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Mission District': 17,
        'Union Square': 22,
        'Pacific Heights': 16,
        'Bayview': 23,
        'Fisherman\'s Wharf': 24,
        'Marina District': 16,
        'Richmond District': 7,
        'Sunset District': 10
    }
}

# People data: {name: {'location': str, 'available_start': str, 'available_end': str, 'duration': int}}
people = {
    'Elizabeth': {'location': 'Mission District', 'available_start': '10:30', 'available_end': '20:00', 'duration': 90},
    'David': {'location': 'Union Square', 'available_start': '15:15', 'available_end': '19:00', 'duration': 45},
    'Sandra': {'location': 'Pacific Heights', 'available_start': '7:00', 'available_end': '20:00', 'duration': 120},
    'Thomas': {'location': 'Bayview', 'available_start': '19:30', 'available_end': '20:30', 'duration': 30},
    'Robert': {'location': 'Fisherman\'s Wharf', 'available_start': '10:00', 'available_end': '15:00', 'duration': 15},
    'Kenneth': {'location': 'Marina District', 'available_start': '10:45', 'available_end': '13:00', 'duration': 45},
    'Melissa': {'location': 'Richmond District', 'available_start': '18:15', 'available_end': '20:00', 'duration': 15},
    'Kimberly': {'location': 'Sunset District', 'available_start': '10:15', 'available_end': '18:15', 'duration': 105},
    'Amanda': {'location': 'Golden Gate Park', 'available_start': '7:45', 'available_end': '18:45', 'duration': 15}
}

def get_travel_time(from_loc, to_loc):
    return travel_times.get(from_loc, {}).get(to_loc, float('inf'))

def evaluate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Haight-Ashbury'
    schedule = []
    total_meetings = 0
    
    for person in order:
        data = people[person]
        location = data['location']
        travel_time = get_travel_time(current_location, location)
        
        if travel_time == float('inf'):
            return None, 0
        
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(data['available_start'])
        available_end = time_to_minutes(data['available_end'])
        duration = data['duration']
        
        # Calculate meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + duration
        
        if meeting_end > available_end:
            return None, 0
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': person,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
        total_meetings += 1
    
    return schedule, total_meetings

def find_optimal_schedule():
    best_schedule = None
    best_count = 0
    
    # Try all permutations of people to find the maximum number of meetings
    for perm in permutations(people.keys()):
        schedule, count = evaluate_schedule(perm)
        if count > best_count:
            best_schedule = schedule
            best_count = count
        elif count == best_count and schedule:
            # Prefer schedules that end earlier
            if time_to_minutes(schedule[-1]['end_time']) < time_to_minutes(best_schedule[-1]['end_time']):
                best_schedule = schedule
    
    return best_schedule

optimal_schedule = find_optimal_schedule()

result = {
    "itinerary": optimal_schedule
}

print(json.dumps(result, indent=2))