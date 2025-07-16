import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input data (unchanged)
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

friends = [
    {'name': 'Steven', 'location': 'North Beach', 'start': '17:30', 'end': '20:30', 'duration': 15},
    {'name': 'Sarah', 'location': 'Golden Gate Park', 'start': '17:00', 'end': '19:15', 'duration': 75},
    {'name': 'Brian', 'location': 'Embarcadero', 'start': '14:15', 'end': '16:00', 'duration': 105},
    {'name': 'Stephanie', 'location': 'Haight-Ashbury', 'start': '10:15', 'end': '12:15', 'duration': 75},
    {'name': 'Melissa', 'location': 'Richmond District', 'start': '14:00', 'end': '19:30', 'duration': 30},
    {'name': 'Nancy', 'location': 'Nob Hill', 'start': '8:15', 'end': '12:45', 'duration': 90},
    {'name': 'David', 'location': 'Marina District', 'start': '11:15', 'end': '13:15', 'duration': 120},
    {'name': 'James', 'location': 'Presidio', 'start': '15:00', 'end': '18:15', 'duration': 120},
    {'name': 'Elizabeth', 'location': 'Union Square', 'start': '11:30', 'end': '21:00', 'duration': 60},
    {'name': 'Robert', 'location': 'Financial District', 'start': '13:15', 'end': '15:15', 'duration': 45}
]

def get_travel_time(from_loc, to_loc):
    return travel_times.get(from_loc, {}).get(to_loc, float('inf'))

def is_schedule_valid(schedule):
    current_time = time_to_minutes('9:00')
    current_location = 'The Castro'
    
    for entry in schedule:
        # Travel to friend's location
        travel_time = get_travel_time(current_location, entry['location'])
        arrival_time = current_time + travel_time
        
        # Check if arrival is before friend's availability ends
        friend_end = time_to_minutes(entry['end'])
        if arrival_time >= friend_end:
            return False
        
        # Calculate meeting start and end
        meeting_start = max(arrival_time, time_to_minutes(entry['start']))
        meeting_end = meeting_start + entry['duration']
        
        # Check if meeting fits in friend's availability
        if meeting_end > friend_end:
            return False
        
        # Update current time and location
        current_time = meeting_end
        current_location = entry['location']
    
    return True

def calculate_total_meeting_time(schedule):
    return sum(entry['duration'] for entry in schedule)

def generate_possible_schedules():
    # Filter friends that can be potentially met (duration <= available time)
    possible_friends = []
    for friend in friends:
        available_time = time_to_minutes(friend['end']) - time_to_minutes(friend['start'])
        if friend['duration'] <= available_time:
            possible_friends.append(friend)
    
    # Generate permutations of different lengths, prioritizing longer schedules
    best_schedule = []
    best_time = 0
    
    # Try all possible lengths from longest to shortest
    for r in range(len(possible_friends), 0, -1):
        for perm in permutations(possible_friends, r):
            # Check if all friends in permutation are unique
            names = [p['name'] for p in perm]
            if len(names) != len(set(names)):
                continue
            
            # Check if schedule is valid
            if is_schedule_valid(perm):
                total_time = calculate_total_meeting_time(perm)
                # If we found a schedule with all friends, return it immediately
                if r == len(possible_friends):
                    return perm
                # Otherwise track the best partial schedule
                if total_time > best_time:
                    best_time = total_time
                    best_schedule = perm
        # If we found any valid schedule at this length, return the best one
        if best_schedule:
            return best_schedule
    
    return best_schedule

def build_itinerary(schedule):
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'The Castro'
    
    for entry in schedule:
        # Travel to friend's location
        travel_time = get_travel_time(current_location, entry['location'])
        arrival_time = current_time + travel_time
        
        # Calculate meeting time
        meeting_start = max(arrival_time, time_to_minutes(entry['start']))
        meeting_end = meeting_start + entry['duration']
        
        # Add travel and meeting to itinerary
        if current_location != entry['location']:
            itinerary.append({
                'action': 'travel',
                'from': current_location,
                'to': entry['location'],
                'start_time': minutes_to_time(current_time),
                'end_time': minutes_to_time(arrival_time)
            })
        
        itinerary.append({
            'action': 'meet',
            'location': entry['location'],
            'person': entry['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = entry['location']
    
    return {'itinerary': itinerary}

# Main execution
best_schedule = generate_possible_schedules()
result = build_itinerary(best_schedule)
print(json.dumps(result, indent=2))