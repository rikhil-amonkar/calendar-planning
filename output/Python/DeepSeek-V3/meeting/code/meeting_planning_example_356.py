import json
from itertools import permutations

def time_to_minutes(time_str):
    if time_str.endswith('AM'):
        time_str = time_str[:-2].strip()
        hours, minutes = map(int, time_str.split(':'))
        if hours == 12:
            hours = 0
    elif time_str.endswith('PM'):
        time_str = time_str[:-2].strip()
        hours, minutes = map(int, time_str.split(':'))
        if hours != 12:
            hours += 12
    else:
        hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times in minutes
travel_times = {
    'Bayview': {
        'North Beach': 21,
        'Presidio': 31,
        'Haight-Ashbury': 19,
        'Union Square': 17
    },
    'North Beach': {
        'Bayview': 22,
        'Presidio': 17,
        'Haight-Ashbury': 18,
        'Union Square': 7
    },
    'Presidio': {
        'Bayview': 31,
        'North Beach': 18,
        'Haight-Ashbury': 15,
        'Union Square': 22
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'North Beach': 19,
        'Presidio': 15,
        'Union Square': 17
    },
    'Union Square': {
        'Bayview': 15,
        'North Beach': 10,
        'Presidio': 24,
        'Haight-Ashbury': 18
    }
}

# Constraints
arrival_time = time_to_minutes('9:00AM')
friends = {
    'Barbara': {
        'location': 'North Beach',
        'start': time_to_minutes('1:45PM'),
        'end': time_to_minutes('8:15PM'),
        'duration': 60
    },
    'Margaret': {
        'location': 'Presidio',
        'start': time_to_minutes('10:15AM'),
        'end': time_to_minutes('3:15PM'),
        'duration': 30
    },
    'Kevin': {
        'location': 'Haight-Ashbury',
        'start': time_to_minutes('8:00PM'),
        'end': time_to_minutes('8:45PM'),
        'duration': 30
    },
    'Kimberly': {
        'location': 'Union Square',
        'start': time_to_minutes('7:45AM'),
        'end': time_to_minutes('4:45PM'),
        'duration': 30
    }
}

def calculate_schedule(order):
    current_time = arrival_time
    current_location = 'Bayview'
    schedule = []
    for friend in order:
        friend_info = friends[friend]
        location = friend_info['location']
        travel_time = travel_times[current_location][location]
        arrival = current_time + travel_time
        start = max(arrival, friend_info['start'])
        end = start + friend_info['duration']
        if end > friend_info['end']:
            return None
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': friend,
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end)
        })
        current_time = end
        current_location = location
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return -1
    return len(schedule)

best_schedule = None
best_score = -1

# Try all possible orders of meeting friends
for order in permutations(friends.keys()):
    schedule = calculate_schedule(order)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule

# Output the best schedule
output = {
    "itinerary": best_schedule if best_schedule else []
}

print(json.dumps(output, indent=2))