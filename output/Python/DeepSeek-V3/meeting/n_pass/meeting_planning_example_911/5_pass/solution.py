import json
from itertools import combinations

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

def schedule_friends(start_time, start_location, friends_to_schedule):
    current_time = time_to_minutes(start_time)
    current_location = start_location
    scheduled = []
    
    for friend in sorted(friends_to_schedule, key=lambda x: time_to_minutes(x['end'])):
        # Travel to friend's location
        travel_time = get_travel_time(current_location, friend['location'])
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        friend_start = time_to_minutes(friend['start'])
        friend_end = time_to_minutes(friend['end'])
        
        if arrival_time > friend_end:
            continue  # Can't make it in time
            
        meeting_start = max(arrival_time, friend_start)
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > friend_end:
            continue  # Not enough time for full meeting
            
        # Schedule this friend
        scheduled.append({
            'friend': friend,
            'travel_time': travel_time,
            'arrival_time': arrival_time,
            'meeting_start': meeting_start,
            'meeting_end': meeting_end
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = friend['location']
    
    return scheduled

def find_optimal_schedule():
    max_friends = 0
    best_schedule = []
    
    # Try all possible combinations of friends, starting with largest possible
    for r in range(len(friends), 0, -1):
        for friend_combination in combinations(friends, r):
            scheduled = schedule_friends('9:00', 'The Castro', friend_combination)
            
            # Check if this is better than our current best
            if len(scheduled) > max_friends or (
                len(scheduled) == max_friends and 
                sum(f['friend']['duration'] for f in scheduled) > sum(f['friend']['duration'] for f in best_schedule)
            ):
                max_friends = len(scheduled)
                best_schedule = scheduled
                
                # Early exit if we've found the theoretical maximum
                if max_friends == len(friends):
                    return best_schedule
    
    return best_schedule

def build_itinerary(scheduled_friends):
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'The Castro'
    
    for entry in scheduled_friends:
        friend = entry['friend']
        
        # Add travel if needed
        if current_location != friend['location']:
            itinerary.append({
                'action': 'travel',
                'from': current_location,
                'to': friend['location'],
                'start_time': minutes_to_time(current_time),
                'end_time': minutes_to_time(entry['arrival_time'])
            })
        
        # Add meeting
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(entry['meeting_start']),
            'end_time': minutes_to_time(entry['meeting_end'])
        })
        
        # Update current time and location
        current_time = entry['meeting_end']
        current_location = friend['location']
    
    return {'itinerary': itinerary}

# Main execution
optimal_schedule = find_optimal_schedule()
result = build_itinerary(optimal_schedule)
print(json.dumps(result, indent=2))