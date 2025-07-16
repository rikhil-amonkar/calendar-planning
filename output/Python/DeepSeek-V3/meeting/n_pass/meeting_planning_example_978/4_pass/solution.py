import json
from itertools import permutations

# Travel times between locations in minutes
travel_times = {
    'Embarcadero': {
        'Embarcadero': 0,
        'Union Square': 10,
        'Fisherman\'s Wharf': 15,
        'North Beach': 12,
        'Mission District': 20
    },
    'Union Square': {
        'Embarcadero': 10,
        'Union Square': 0,
        'Fisherman\'s Wharf': 8,
        'North Beach': 6,
        'Mission District': 15
    },
    'Fisherman\'s Wharf': {
        'Embarcadero': 15,
        'Union Square': 8,
        'Fisherman\'s Wharf': 0,
        'North Beach': 5,
        'Mission District': 18
    },
    'North Beach': {
        'Embarcadero': 12,
        'Union Square': 6,
        'Fisherman\'s Wharf': 5,
        'North Beach': 0,
        'Mission District': 16
    },
    'Mission District': {
        'Embarcadero': 20,
        'Union Square': 15,
        'Fisherman\'s Wharf': 18,
        'North Beach': 16,
        'Mission District': 0
    }
}

# Friends' availability data
friends = [
    {'name': 'Alice', 'location': 'Union Square', 'start': 9.5, 'end': 11.0, 'duration': 0.5},
    {'name': 'Bob', 'location': 'Fisherman\'s Wharf', 'start': 10.0, 'end': 12.0, 'duration': 1.0},
    {'name': 'Charlie', 'location': 'North Beach', 'start': 9.0, 'end': 10.5, 'duration': 0.5},
    {'name': 'Dana', 'location': 'Mission District', 'start': 11.0, 'end': 12.5, 'duration': 0.5},
    {'name': 'Eve', 'location': 'Union Square', 'start': 10.5, 'end': 12.0, 'duration': 0.5}
]

def float_to_time(time_float):
    """Convert float time (9.5) to time string (9:30)"""
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule(permutation):
    current_time = 9.0  # Start at Embarcadero at 9:00
    current_location = 'Embarcadero'
    schedule = []
    total_meetings = 0
    
    for friend in permutation:
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']] / 60.0
        arrival_time = current_time + travel_time
        
        # Calculate meeting window
        meeting_start = max(arrival_time, friend['start'])
        meeting_end = meeting_start + friend['duration']
        
        # Check if meeting fits in friend's availability and we can arrive on time
        if meeting_end <= friend['end']:
            # Add to schedule
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': float_to_time(meeting_start),
                'end_time': float_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend['location']
            total_meetings += 1
    
    return schedule, total_meetings

def find_optimal_schedule():
    best_schedule = []
    max_meetings = 0
    
    # Try all possible combinations of friends (from 1 to 5 friends)
    for r in range(5, 0, -1):
        for perm in permutations(friends, r):
            schedule, count = calculate_schedule(perm)
            if count > max_meetings or (count == max_meetings and len(schedule) > len(best_schedule)):
                max_meetings = count
                best_schedule = schedule
                # Early exit if we found the maximum possible meetings
                if max_meetings == 5:
                    return best_schedule
    
    return best_schedule

# Generate the optimal schedule
optimal_schedule = find_optimal_schedule()

# Output as JSON
output = {
    "itinerary": optimal_schedule
}

print(json.dumps(output, indent=2))