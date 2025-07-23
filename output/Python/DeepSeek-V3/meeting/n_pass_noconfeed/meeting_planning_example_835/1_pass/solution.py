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
    'Pacific Heights': {
        'Golden Gate Park': 15,
        'The Castro': 16,
        'Bayview': 22,
        'Marina District': 6,
        'Union Square': 12,
        'Sunset District': 21,
        'Alamo Square': 10,
        'Financial District': 13,
        'Mission District': 15
    },
    'Golden Gate Park': {
        'Pacific Heights': 16,
        'The Castro': 13,
        'Bayview': 23,
        'Marina District': 16,
        'Union Square': 22,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'Mission District': 17
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
        'Bayview': 19,
        'Marina District': 21,
        'Union Square': 19,
        'Sunset District': 17,
        'Alamo Square': 8,
        'Financial District': 21,
        'Mission District': 7
    },
    'Bayview': {
        'Pacific Heights': 23,
        'Golden Gate Park': 22,
        'The Castro': 19,
        'Marina District': 27,
        'Union Square': 18,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'Mission District': 13
    },
    'Marina District': {
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'The Castro': 22,
        'Bayview': 27,
        'Union Square': 16,
        'Sunset District': 19,
        'Alamo Square': 15,
        'Financial District': 17,
        'Mission District': 20
    },
    'Union Square': {
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'The Castro': 17,
        'Bayview': 15,
        'Marina District': 18,
        'Sunset District': 27,
        'Alamo Square': 15,
        'Financial District': 9,
        'Mission District': 14
    },
    'Sunset District': {
        'Pacific Heights': 21,
        'Golden Gate Park': 11,
        'The Castro': 17,
        'Bayview': 22,
        'Marina District': 21,
        'Union Square': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'Mission District': 25
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'The Castro': 8,
        'Bayview': 16,
        'Marina District': 15,
        'Union Square': 14,
        'Sunset District': 16,
        'Financial District': 17,
        'Mission District': 10
    },
    'Financial District': {
        'Pacific Heights': 13,
        'Golden Gate Park': 23,
        'The Castro': 20,
        'Bayview': 19,
        'Marina District': 15,
        'Union Square': 9,
        'Sunset District': 30,
        'Alamo Square': 17,
        'Mission District': 17
    },
    'Mission District': {
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
        'The Castro': 7,
        'Bayview': 14,
        'Marina District': 19,
        'Union Square': 15,
        'Sunset District': 24,
        'Alamo Square': 11,
        'Financial District': 15
    }
}

friends = [
    {'name': 'Helen', 'location': 'Golden Gate Park', 'start': '9:30', 'end': '12:15', 'duration': 45},
    {'name': 'Steven', 'location': 'The Castro', 'start': '20:15', 'end': '22:00', 'duration': 105},
    {'name': 'Deborah', 'location': 'Bayview', 'start': '8:30', 'end': '12:00', 'duration': 30},
    {'name': 'Matthew', 'location': 'Marina District', 'start': '9:15', 'end': '14:15', 'duration': 45},
    {'name': 'Joseph', 'location': 'Union Square', 'start': '14:15', 'end': '18:45', 'duration': 120},
    {'name': 'Ronald', 'location': 'Sunset District', 'start': '16:00', 'end': '20:45', 'duration': 60},
    {'name': 'Robert', 'location': 'Alamo Square', 'start': '18:30', 'end': '21:15', 'duration': 120},
    {'name': 'Rebecca', 'location': 'Financial District', 'start': '14:45', 'end': '16:15', 'duration': 30},
    {'name': 'Elizabeth', 'location': 'Mission District', 'start': '18:30', 'end': '21:00', 'duration': 120}
]

current_location = 'Pacific Heights'
current_time = time_to_minutes('9:00')

def find_best_schedule():
    best_schedule = []
    max_meetings = 0
    # Try all permutations of friends to find the best schedule
    for perm in permutations(friends):
        schedule = []
        loc = current_location
        time = current_time
        for friend in perm:
            travel_time = travel_times[loc][friend['location']]
            arrival_time = time + travel_time
            friend_start = time_to_minutes(friend['start'])
            friend_end = time_to_minutes(friend['end'])
            
            # Calculate possible meeting window
            meeting_start = max(arrival_time, friend_start)
            meeting_end = min(meeting_start + friend['duration'], friend_end)
            
            if meeting_end - meeting_start >= friend['duration']:
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                time = meeting_end
                loc = friend['location']
        
        if len(schedule) > max_meetings:
            max_meetings = len(schedule)
            best_schedule = schedule
    
    return best_schedule

best_schedule = find_best_schedule()
output = {'itinerary': best_schedule}
print(json.dumps(output, indent=2))