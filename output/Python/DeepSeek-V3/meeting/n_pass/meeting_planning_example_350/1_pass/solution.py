import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_times = {
    'Bayview': {
        'Pacific Heights': 23,
        'Mission District': 13,
        'Haight-Ashbury': 19,
        'Financial District': 19
    },
    'Pacific Heights': {
        'Bayview': 22,
        'Mission District': 15,
        'Haight-Ashbury': 11,
        'Financial District': 13
    },
    'Mission District': {
        'Bayview': 15,
        'Pacific Heights': 16,
        'Haight-Ashbury': 12,
        'Financial District': 17
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'Pacific Heights': 12,
        'Mission District': 11,
        'Financial District': 21
    },
    'Financial District': {
        'Bayview': 19,
        'Pacific Heights': 13,
        'Mission District': 17,
        'Haight-Ashbury': 19
    }
}

friends = {
    'Mary': {
        'location': 'Pacific Heights',
        'available_start': '10:00',
        'available_end': '19:00',
        'min_duration': 45
    },
    'Lisa': {
        'location': 'Mission District',
        'available_start': '20:30',
        'available_end': '22:00',
        'min_duration': 75
    },
    'Betty': {
        'location': 'Haight-Ashbury',
        'available_start': '7:15',
        'available_end': '17:15',
        'min_duration': 90
    },
    'Charles': {
        'location': 'Financial District',
        'available_start': '11:15',
        'available_end': '15:00',
        'min_duration': 120
    }
}

current_location = 'Bayview'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    for friend in order:
        info = friends[friend]
        dest = info['location']
        travel = travel_times[loc][dest]
        arrival = time + travel
        start = max(arrival, time_to_minutes(info['available_start']))
        end = min(start + info['min_duration'], time_to_minutes(info['available_end']))
        if end <= time_to_minutes(info['available_end']) and start < end:
            schedule.append({
                'action': 'meet',
                'location': dest,
                'person': friend,
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            time = end
            loc = dest
        else:
            return None
    return schedule

best_schedule = None
max_meetings = 0

# Try all possible orders of meetings
for order in permutations(friends.keys()):
    schedule = calculate_schedule(order)
    if schedule and len(schedule) > max_meetings:
        best_schedule = schedule
        max_meetings = len(schedule)
    elif schedule and len(schedule) == max_meetings:
        # Prefer longer total meeting time
        current_total = sum(friends[item['person']]['min_duration'] for item in best_schedule) if best_schedule else 0
        new_total = sum(friends[item['person']]['min_duration'] for item in schedule)
        if new_total > current_total:
            best_schedule = schedule

# Ensure we meet Lisa last if possible
if best_schedule and any(item['person'] == 'Lisa' for item in best_schedule):
    lisa_index = next(i for i, item in enumerate(best_schedule) if item['person'] == 'Lisa')
    if lisa_index != len(best_schedule) - 1:
        # Move Lisa to the end
        lisa_item = best_schedule.pop(lisa_index)
        best_schedule.append(lisa_item)

output = {
    "itinerary": best_schedule if best_schedule else []
}

print(json.dumps(output, indent=2))