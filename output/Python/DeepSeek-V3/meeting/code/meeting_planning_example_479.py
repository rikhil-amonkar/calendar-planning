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
    'Embarcadero': {
        'Golden Gate Park': 25,
        'Haight-Ashbury': 21,
        'Bayview': 21,
        'Presidio': 20,
        'Financial District': 5
    },
    'Golden Gate Park': {
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Bayview': 23,
        'Presidio': 11,
        'Financial District': 26
    },
    'Haight-Ashbury': {
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Bayview': 18,
        'Presidio': 15,
        'Financial District': 21
    },
    'Bayview': {
        'Embarcadero': 19,
        'Golden Gate Park': 22,
        'Haight-Ashbury': 19,
        'Presidio': 31,
        'Financial District': 19
    },
    'Presidio': {
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Haight-Ashbury': 15,
        'Bayview': 31,
        'Financial District': 23
    },
    'Financial District': {
        'Embarcadero': 4,
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Bayview': 19,
        'Presidio': 22
    }
}

friends = {
    'Mary': {
        'location': 'Golden Gate Park',
        'start': time_to_minutes('8:45'),
        'end': time_to_minutes('11:45'),
        'duration': 45
    },
    'Kevin': {
        'location': 'Haight-Ashbury',
        'start': time_to_minutes('10:15'),
        'end': time_to_minutes('16:15'),
        'duration': 90
    },
    'Deborah': {
        'location': 'Bayview',
        'start': time_to_minutes('15:00'),
        'end': time_to_minutes('19:15'),
        'duration': 120
    },
    'Stephanie': {
        'location': 'Presidio',
        'start': time_to_minutes('10:00'),
        'end': time_to_minutes('17:15'),
        'duration': 120
    },
    'Emily': {
        'location': 'Financial District',
        'start': time_to_minutes('11:30'),
        'end': time_to_minutes('21:45'),
        'duration': 105
    }
}

def calculate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Embarcadero'
    schedule = []
    
    for friend in order:
        friend_data = friends[friend]
        location = friend_data['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        # Calculate meeting window
        start_window = friend_data['start']
        end_window = friend_data['end']
        duration = friend_data['duration']
        
        # Determine meeting start time
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + duration
        
        if meeting_end > end_window:
            return None  # Not enough time to meet
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': friend,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
    
    return schedule

# Generate all possible orders of meeting friends
all_orders = permutations(friends.keys())

best_schedule = None
max_meetings = 0

for order in all_orders:
    schedule = calculate_schedule(order)
    if schedule is not None and len(schedule) > max_meetings:
        max_meetings = len(schedule)
        best_schedule = schedule

if best_schedule is None:
    # Try to find a schedule with fewer meetings if all 5 is impossible
    for num_meetings in range(4, 0, -1):
        from itertools import combinations
        for friends_subset in combinations(friends.keys(), num_meetings):
            for order in permutations(friends_subset):
                schedule = calculate_schedule(order)
                if schedule is not None:
                    best_schedule = schedule
                    break
            if best_schedule is not None:
                break
        if best_schedule is not None:
            break

output = {
    "itinerary": best_schedule if best_schedule is not None else []
}

print(json.dumps(output, indent=2))