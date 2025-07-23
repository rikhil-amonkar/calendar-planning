import json
from itertools import permutations

def time_to_minutes(time_str):
    if time_str == '24:00':
        return 24 * 60
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
travel_times = {
    'Pacific Heights': {
        'Nob Hill': 8,
        'Russian Hill': 7,
        'The Castro': 16,
        'Sunset District': 21,
        'Haight-Ashbury': 11
    },
    'Nob Hill': {
        'Pacific Heights': 8,
        'Russian Hill': 5,
        'The Castro': 17,
        'Sunset District': 25,
        'Haight-Ashbury': 13
    },
    'Russian Hill': {
        'Pacific Heights': 7,
        'Nob Hill': 5,
        'The Castro': 21,
        'Sunset District': 23,
        'Haight-Ashbury': 17
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Nob Hill': 16,
        'Russian Hill': 18,
        'Sunset District': 17,
        'Haight-Ashbury': 6
    },
    'Sunset District': {
        'Pacific Heights': 21,
        'Nob Hill': 27,
        'Russian Hill': 24,
        'The Castro': 17,
        'Haight-Ashbury': 15
    },
    'Haight-Ashbury': {
        'Pacific Heights': 12,
        'Nob Hill': 15,
        'Russian Hill': 17,
        'The Castro': 6,
        'Sunset District': 15
    }
}

friends = [
    {
        'name': 'Ronald',
        'location': 'Nob Hill',
        'available_start': '10:00',
        'available_end': '17:00',
        'duration': 105
    },
    {
        'name': 'Sarah',
        'location': 'Russian Hill',
        'available_start': '7:15',
        'available_end': '9:30',
        'duration': 45
    },
    {
        'name': 'Helen',
        'location': 'The Castro',
        'available_start': '13:30',
        'available_end': '17:00',
        'duration': 120
    },
    {
        'name': 'Joshua',
        'location': 'Sunset District',
        'available_start': '14:15',
        'available_end': '19:30',
        'duration': 90
    },
    {
        'name': 'Margaret',
        'location': 'Haight-Ashbury',
        'available_start': '10:15',
        'available_end': '22:00',
        'duration': 60
    }
]

current_time = time_to_minutes('9:00')
current_location = 'Pacific Heights'

# Generate all possible orders of meeting friends
friend_indices = [0, 1, 2, 3, 4]  # Ronald, Sarah, Helen, Joshua, Margaret
best_schedule = None
max_meetings = 0

# Since Sarah is only available early, we'll handle her separately
sarah_index = 1
other_indices = [0, 2, 3, 4]

# Try all permutations of the other friends
for perm in permutations(other_indices):
    # Try inserting Sarah at different positions
    for insert_pos in range(len(perm) + 1):
        schedule = list(perm[:insert_pos]) + [sarah_index] + list(perm[insert_pos:])
        
        temp_time = current_time
        temp_location = current_location
        itinerary = []
        valid = True
        meetings = 0
        
        for friend_idx in schedule:
            friend = friends[friend_idx]
            loc = friend['location']
            travel_time = travel_times[temp_location][loc]
            arrive_time = temp_time + travel_time
            
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            duration = friend['duration']
            
            # Calculate meeting window
            start_time = max(arrive_time, available_start)
            end_time = start_time + duration
            
            if end_time > available_end:
                valid = False
                break
            
            itinerary.append({
                'action': 'meet',
                'location': loc,
                'person': friend['name'],
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            
            meetings += 1
            temp_time = end_time
            temp_location = loc
        
        if valid and meetings > max_meetings:
            max_meetings = meetings
            best_schedule = itinerary
        elif valid and meetings == max_meetings:
            # Prefer schedules that meet more people or have longer meetings
            if not best_schedule or len(itinerary) > len(best_schedule):
                best_schedule = itinerary

# After trying all permutations, output the best schedule
if best_schedule:
    result = {'itinerary': best_schedule}
else:
    result = {'itinerary': []}

print(json.dumps(result, indent=2))