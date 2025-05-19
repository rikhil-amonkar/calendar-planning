import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Embarcadero': {
        'Fisherman\'s Wharf': 6,
        'Financial District': 5,
        'Russian Hill': 8,
        'Marina District': 12,
        'Richmond District': 21,
        'Pacific Heights': 11,
        'Haight-Ashbury': 21,
        'Presidio': 20,
        'Nob Hill': 10,
        'The Castro': 25
    },
    'Fisherman\'s Wharf': {
        'Embarcadero': 8,
        'Financial District': 11,
        'Russian Hill': 7,
        'Marina District': 9,
        'Richmond District': 18,
        'Pacific Heights': 12,
        'Haight-Ashbury': 22,
        'Presidio': 17,
        'Nob Hill': 11,
        'The Castro': 27
    },
    'Financial District': {
        'Embarcadero': 4,
        'Fisherman\'s Wharf': 10,
        'Russian Hill': 11,
        'Marina District': 15,
        'Richmond District': 21,
        'Pacific Heights': 13,
        'Haight-Ashbury': 19,
        'Presidio': 22,
        'Nob Hill': 8,
        'The Castro': 20
    },
    'Russian Hill': {
        'Embarcadero': 8,
        'Fisherman\'s Wharf': 7,
        'Financial District': 11,
        'Marina District': 7,
        'Richmond District': 14,
        'Pacific Heights': 7,
        'Haight-Ashbury': 17,
        'Presidio': 14,
        'Nob Hill': 5,
        'The Castro': 21
    },
    'Marina District': {
        'Embarcadero': 14,
        'Fisherman\'s Wharf': 10,
        'Financial District': 17,
        'Russian Hill': 8,
        'Richmond District': 11,
        'Pacific Heights': 7,
        'Haight-Ashbury': 16,
        'Presidio': 10,
        'Nob Hill': 12,
        'The Castro': 22
    },
    'Richmond District': {
        'Embarcadero': 19,
        'Fisherman\'s Wharf': 18,
        'Financial District': 22,
        'Russian Hill': 13,
        'Marina District': 9,
        'Pacific Heights': 10,
        'Haight-Ashbury': 10,
        'Presidio': 7,
        'Nob Hill': 17,
        'The Castro': 16
    },
    'Pacific Heights': {
        'Embarcadero': 10,
        'Fisherman\'s Wharf': 13,
        'Financial District': 13,
        'Russian Hill': 7,
        'Marina District': 6,
        'Richmond District': 12,
        'Haight-Ashbury': 11,
        'Presidio': 11,
        'Nob Hill': 8,
        'The Castro': 16
    },
    'Haight-Ashbury': {
        'Embarcadero': 20,
        'Fisherman\'s Wharf': 23,
        'Financial District': 21,
        'Russian Hill': 17,
        'Marina District': 17,
        'Richmond District': 10,
        'Pacific Heights': 12,
        'Presidio': 15,
        'Nob Hill': 15,
        'The Castro': 6
    },
    'Presidio': {
        'Embarcadero': 20,
        'Fisherman\'s Wharf': 19,
        'Financial District': 23,
        'Russian Hill': 14,
        'Marina District': 11,
        'Richmond District': 7,
        'Pacific Heights': 11,
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'The Castro': 21
    },
    'Nob Hill': {
        'Embarcadero': 9,
        'Fisherman\'s Wharf': 10,
        'Financial District': 9,
        'Russian Hill': 5,
        'Marina District': 11,
        'Richmond District': 14,
        'Pacific Heights': 8,
        'Haight-Ashbury': 13,
        'Presidio': 17,
        'The Castro': 16
    },
    'The Castro': {
        'Embarcadero': 22,
        'Fisherman\'s Wharf': 24,
        'Financial District': 21,
        'Russian Hill': 18,
        'Marina District': 21,
        'Richmond District': 16,
        'Pacific Heights': 16,
        'Haight-Ashbury': 6,
        'Presidio': 20,
        'Nob Hill': 16
    }
}

# Friend availability
friends = {
    'Stephanie': {'location': 'Fisherman\'s Wharf', 'start': 15.5, 'end': 22.0, 'duration': 0.5},
    'Lisa': {'location': 'Financial District', 'start': 10.75, 'end': 17.25, 'duration': 0.25},
    'Melissa': {'location': 'Russian Hill', 'start': 17.0, 'end': 21.75, 'duration': 2.0},
    'Betty': {'location': 'Marina District', 'start': 10.75, 'end': 14.25, 'duration': 1.0},
    'Sarah': {'location': 'Richmond District', 'start': 16.25, 'end': 19.5, 'duration': 1.75},
    'Daniel': {'location': 'Pacific Heights', 'start': 18.5, 'end': 21.75, 'duration': 1.0},
    'Joshua': {'location': 'Haight-Ashbury', 'start': 9.0, 'end': 15.5, 'duration': 0.25},
    'Joseph': {'location': 'Presidio', 'start': 7.0, 'end': 13.0, 'duration': 0.75},
    'Andrew': {'location': 'Nob Hill', 'start': 19.75, 'end': 22.0, 'duration': 1.75},
    'John': {'location': 'The Castro', 'start': 13.25, 'end': 19.75, 'duration': 0.75}
}

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule(order):
    current_time = 9.0  # Start at Embarcadero at 9:00
    current_location = 'Embarcadero'
    schedule = []
    
    for friend_name in order:
        friend = friends[friend_name]
        location = friend['location']
        
        # Calculate travel time
        travel_time = travel_times[current_location][location] / 60.0
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        start_window = friend['start']
        end_window = friend['end']
        
        # Determine meeting start time
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > end_window:
            return None  # Can't meet this friend
        
        # Add to schedule
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': friend_name,
            'start_time': float_to_time(meeting_start),
            'end_time': float_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return 0
    return len(schedule)

# Generate possible orders and find the best one
best_schedule = []
best_score = 0

# We'll try permutations of a subset since full permutations would be too slow
for order in permutations(friends.keys(), 5):
    schedule = calculate_schedule(order)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule
    if best_score == len(friends):
        break

# If we didn't find a full schedule, try with fewer friends
if best_score < 5:
    for order in permutations(friends.keys(), 4):
        schedule = calculate_schedule(order)
        score = evaluate_schedule(schedule)
        if score > best_score:
            best_score = score
            best_schedule = schedule
        if best_score == 4:
            break

# Output the best schedule found
result = {
    "itinerary": best_schedule
}

print(json.dumps(result, indent=2))