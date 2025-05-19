import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
travel_times = {
    'Russian Hill': {
        'Presidio': 14,
        'Chinatown': 9,
        'Pacific Heights': 7,
        'Richmond District': 14,
        'Fisherman\'s Wharf': 7,
        'Golden Gate Park': 21,
        'Bayview': 23
    },
    'Presidio': {
        'Russian Hill': 14,
        'Chinatown': 21,
        'Pacific Heights': 11,
        'Richmond District': 7,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 12,
        'Bayview': 31
    },
    'Chinatown': {
        'Russian Hill': 7,
        'Presidio': 19,
        'Pacific Heights': 10,
        'Richmond District': 20,
        'Fisherman\'s Wharf': 8,
        'Golden Gate Park': 23,
        'Bayview': 22
    },
    'Pacific Heights': {
        'Russian Hill': 7,
        'Presidio': 11,
        'Chinatown': 11,
        'Richmond District': 12,
        'Fisherman\'s Wharf': 13,
        'Golden Gate Park': 15,
        'Bayview': 22
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Presidio': 7,
        'Chinatown': 20,
        'Pacific Heights': 10,
        'Fisherman\'s Wharf': 18,
        'Golden Gate Park': 9,
        'Bayview': 26
    },
    'Fisherman\'s Wharf': {
        'Russian Hill': 7,
        'Presidio': 17,
        'Chinatown': 12,
        'Pacific Heights': 12,
        'Richmond District': 18,
        'Golden Gate Park': 25,
        'Bayview': 26
    },
    'Golden Gate Park': {
        'Russian Hill': 19,
        'Presidio': 11,
        'Chinatown': 23,
        'Pacific Heights': 16,
        'Richmond District': 7,
        'Fisherman\'s Wharf': 24,
        'Bayview': 23
    },
    'Bayview': {
        'Russian Hill': 23,
        'Presidio': 31,
        'Chinatown': 18,
        'Pacific Heights': 23,
        'Richmond District': 25,
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22
    }
}

friends = [
    {
        'name': 'Matthew',
        'location': 'Presidio',
        'available_start': '11:00',
        'available_end': '21:00',
        'duration': 90
    },
    {
        'name': 'Margaret',
        'location': 'Chinatown',
        'available_start': '9:15',
        'available_end': '18:45',
        'duration': 90
    },
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'available_start': '14:15',
        'available_end': '17:00',
        'duration': 15
    },
    {
        'name': 'Helen',
        'location': 'Richmond District',
        'available_start': '19:45',
        'available_end': '22:00',
        'duration': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Fisherman\'s Wharf',
        'available_start': '21:15',
        'available_end': '22:15',
        'duration': 60
    },
    {
        'name': 'Kimberly',
        'location': 'Golden Gate Park',
        'available_start': '13:00',
        'available_end': '16:30',
        'duration': 120
    },
    {
        'name': 'Kenneth',
        'location': 'Bayview',
        'available_start': '14:30',
        'available_end': '18:00',
        'duration': 60
    }
]

def generate_schedules():
    current_location = 'Russian Hill'
    current_time = time_to_minutes('9:00')
    max_meetings = 0
    best_schedule = []
    
    # Try all possible orders of meeting friends
    for order in permutations(friends):
        schedule = []
        location = current_location
        time = current_time
        meetings = 0
        
        for friend in order:
            # Check if we can meet this friend
            travel_time = travel_times[location][friend['location']]
            arrival_time = time + travel_time
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            
            # Calculate possible meeting window
            start_time = max(arrival_time, available_start)
            end_time = min(start_time + friend['duration'], available_end)
            
            if end_time > start_time and end_time <= available_end:
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(start_time),
                    'end_time': minutes_to_time(end_time)
                })
                meetings += 1
                time = end_time
                location = friend['location']
            else:
                # Try to adjust meeting time if possible
                if available_end - available_start >= friend['duration']:
                    start_time = available_start
                    end_time = start_time + friend['duration']
                    if arrival_time <= start_time:
                        schedule.append({
                            'action': 'meet',
                            'location': friend['location'],
                            'person': friend['name'],
                            'start_time': minutes_to_time(start_time),
                            'end_time': minutes_to_time(end_time)
                        })
                        meetings += 1
                        time = end_time
                        location = friend['location']
        
        if meetings > max_meetings or (meetings == max_meetings and len(schedule) > len(best_schedule)):
            max_meetings = meetings
            best_schedule = schedule
    
    return best_schedule

# Generate the best schedule
best_schedule = generate_schedules()

# Output as JSON
output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))