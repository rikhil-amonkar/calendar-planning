import json
from itertools import permutations

# Travel times dictionary
travel_times = {
    'Union Square': {
        'The Castro': 17,
        'North Beach': 10,
        'Embarcadero': 11,
        'Alamo Square': 15,
        'Nob Hill': 9,
        'Presidio': 24,
        'Fisherman\'s Wharf': 15,
        'Mission District': 14,
        'Haight-Ashbury': 18
    },
    'The Castro': {
        'Union Square': 19,
        'North Beach': 20,
        'Embarcadero': 22,
        'Alamo Square': 8,
        'Nob Hill': 16,
        'Presidio': 20,
        'Fisherman\'s Wharf': 24,
        'Mission District': 7,
        'Haight-Ashbury': 6
    },
    'North Beach': {
        'Union Square': 7,
        'The Castro': 23,
        'Embarcadero': 6,
        'Alamo Square': 16,
        'Nob Hill': 7,
        'Presidio': 17,
        'Fisherman\'s Wharf': 5,
        'Mission District': 18,
        'Haight-Ashbury': 18
    },
    'Embarcadero': {
        'Union Square': 10,
        'The Castro': 25,
        'North Beach': 5,
        'Alamo Square': 19,
        'Nob Hill': 10,
        'Presidio': 20,
        'Fisherman\'s Wharf': 6,
        'Mission District': 20,
        'Haight-Ashbury': 21
    },
    'Alamo Square': {
        'Union Square': 14,
        'The Castro': 8,
        'North Beach': 15,
        'Embarcadero': 16,
        'Nob Hill': 11,
        'Presidio': 17,
        'Fisherman\'s Wharf': 19,
        'Mission District': 10,
        'Haight-Ashbury': 5
    },
    'Nob Hill': {
        'Union Square': 7,
        'The Castro': 17,
        'North Beach': 8,
        'Embarcadero': 9,
        'Alamo Square': 11,
        'Presidio': 17,
        'Fisherman\'s Wharf': 10,
        'Mission District': 13,
        'Haight-Ashbury': 13
    },
    'Presidio': {
        'Union Square': 22,
        'The Castro': 21,
        'North Beach': 18,
        'Embarcadero': 20,
        'Alamo Square': 19,
        'Nob Hill': 18,
        'Fisherman\'s Wharf': 19,
        'Mission District': 26,
        'Haight-Ashbury': 15
    },
    'Fisherman\'s Wharf': {
        'Union Square': 13,
        'The Castro': 27,
        'North Beach': 6,
        'Embarcadero': 8,
        'Alamo Square': 21,
        'Nob Hill': 11,
        'Presidio': 17,
        'Mission District': 22,
        'Haight-Ashbury': 22
    },
    'Mission District': {
        'Union Square': 15,
        'The Castro': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Alamo Square': 11,
        'Nob Hill': 12,
        'Presidio': 25,
        'Fisherman\'s Wharf': 22,
        'Haight-Ashbury': 12
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'The Castro': 6,
        'North Beach': 19,
        'Embarcadero': 20,
        'Alamo Square': 5,
        'Nob Hill': 15,
        'Presidio': 15,
        'Fisherman\'s Wharf': 23,
        'Mission District': 11
    }
}

# Friend constraints
friends = [
    {
        'name': 'Melissa',
        'location': 'The Castro',
        'available_start': '20:15',
        'available_end': '21:15',
        'min_duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'North Beach',
        'available_start': '7:00',
        'available_end': '10:30',
        'min_duration': 15
    },
    {
        'name': 'Joseph',
        'location': 'Embarcadero',
        'available_start': '15:30',
        'available_end': '19:30',
        'min_duration': 75
    },
    {
        'name': 'Barbara',
        'location': 'Alamo Square',
        'available_start': '20:45',
        'available_end': '21:45',
        'min_duration': 15
    },
    {
        'name': 'Kenneth',
        'location': 'Nob Hill',
        'available_start': '12:15',
        'available_end': '17:15',
        'min_duration': 105
    },
    {
        'name': 'Joshua',
        'location': 'Presidio',
        'available_start': '16:30',
        'available_end': '18:15',
        'min_duration': 105
    },
    {
        'name': 'Brian',
        'location': 'Fisherman\'s Wharf',
        'available_start': '9:30',
        'available_end': '15:30',
        'min_duration': 45
    },
    {
        'name': 'Steven',
        'location': 'Mission District',
        'available_start': '19:30',
        'available_end': '21:00',
        'min_duration': 90
    },
    {
        'name': 'Betty',
        'location': 'Haight-Ashbury',
        'available_start': '19:00',
        'available_end': '20:30',
        'min_duration': 90
    }
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_schedule(friend, start_time, end_time):
    available_start = time_to_minutes(friend['available_start'])
    available_end = time_to_minutes(friend['available_end'])
    min_duration = friend['min_duration']
    
    # Check if the meeting fits within the friend's availability
    if start_time < available_start or end_time > available_end:
        return False
    
    # Check if the meeting duration is sufficient
    if (end_time - start_time) < min_duration:
        return False
    
    return True

def calculate_schedule(order):
    current_time = time_to_minutes('9:00')  # Start at Union Square at 9:00 AM
    current_location = 'Union Square'
    schedule = []
    
    for friend in order:
        location = friend['location']
        travel_time = travel_times[current_location].get(location, float('inf'))
        
        # Arrival time at friend's location
        arrival_time = current_time + travel_time
        
        # Find the latest possible start time that allows for min_duration
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        # Calculate possible meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = min(meeting_start + min_duration, available_end)
        
        if meeting_end - meeting_start < min_duration:
            return None  # Can't meet this friend with these constraints
        
        # Add to schedule
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = location
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return 0
    
    # Count number of friends met
    return len(schedule)

# Generate all possible friend orders (permutations)
best_schedule = None
best_score = 0

# Since there are too many permutations, we'll use a heuristic approach
# Prioritize friends with tighter time windows first
sorted_friends = sorted(friends, key=lambda x: (
    time_to_minutes(x['available_end']) - time_to_minutes(x['available_start']) - x['min_duration']
))

# Try permutations in order of priority
from itertools import permutations
for perm in permutations(sorted_friends):
    schedule = calculate_schedule(perm)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule
        if best_score == len(friends):  # Found optimal solution
            break

# Output the best schedule found
output = {
    "itinerary": best_schedule if best_schedule else []
}

print(json.dumps(output, indent=2))