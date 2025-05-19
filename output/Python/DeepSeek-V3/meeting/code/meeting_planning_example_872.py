import json
from itertools import permutations

# Convert time string to minutes since 9:00 (540 minutes)
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times dictionary
travel_times = {
    'Presidio': {
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'Russian Hill': 14,
        'North Beach': 18,
        'Chinatown': 21,
        'Union Square': 22,
        'Embarcadero': 20,
        'Financial District': 23,
        'Marina District': 11
    },
    'Haight-Ashbury': {
        'Presidio': 15,
        'Nob Hill': 15,
        'Russian Hill': 17,
        'North Beach': 19,
        'Chinatown': 19,
        'Union Square': 19,
        'Embarcadero': 20,
        'Financial District': 21,
        'Marina District': 17
    },
    'Nob Hill': {
        'Presidio': 17,
        'Haight-Ashbury': 13,
        'Russian Hill': 5,
        'North Beach': 8,
        'Chinatown': 6,
        'Union Square': 7,
        'Embarcadero': 9,
        'Financial District': 9,
        'Marina District': 11
    },
    'Russian Hill': {
        'Presidio': 14,
        'Haight-Ashbury': 17,
        'Nob Hill': 5,
        'North Beach': 5,
        'Chinatown': 9,
        'Union Square': 10,
        'Embarcadero': 8,
        'Financial District': 11,
        'Marina District': 7
    },
    'North Beach': {
        'Presidio': 17,
        'Haight-Ashbury': 18,
        'Nob Hill': 7,
        'Russian Hill': 4,
        'Chinatown': 6,
        'Union Square': 7,
        'Embarcadero': 6,
        'Financial District': 8,
        'Marina District': 9
    },
    'Chinatown': {
        'Presidio': 19,
        'Haight-Ashbury': 19,
        'Nob Hill': 9,
        'Russian Hill': 7,
        'North Beach': 3,
        'Union Square': 7,
        'Embarcadero': 5,
        'Financial District': 5,
        'Marina District': 12
    },
    'Union Square': {
        'Presidio': 24,
        'Haight-Ashbury': 18,
        'Nob Hill': 9,
        'Russian Hill': 13,
        'North Beach': 10,
        'Chinatown': 7,
        'Embarcadero': 11,
        'Financial District': 9,
        'Marina District': 18
    },
    'Embarcadero': {
        'Presidio': 20,
        'Haight-Ashbury': 21,
        'Nob Hill': 10,
        'Russian Hill': 8,
        'North Beach': 5,
        'Chinatown': 7,
        'Union Square': 10,
        'Financial District': 5,
        'Marina District': 12
    },
    'Financial District': {
        'Presidio': 22,
        'Haight-Ashbury': 19,
        'Nob Hill': 8,
        'Russian Hill': 11,
        'North Beach': 7,
        'Chinatown': 5,
        'Union Square': 9,
        'Embarcadero': 4,
        'Marina District': 15
    },
    'Marina District': {
        'Presidio': 10,
        'Haight-Ashbury': 16,
        'Nob Hill': 12,
        'Russian Hill': 8,
        'North Beach': 11,
        'Chinatown': 15,
        'Union Square': 16,
        'Embarcadero': 14,
        'Financial District': 17
    }
}

# Friends data: location, available start, available end, min duration
friends = {
    'Karen': ('Haight-Ashbury', time_to_minutes('21:00'), time_to_minutes('21:45'), 45),
    'Jessica': ('Nob Hill', time_to_minutes('13:45'), time_to_minutes('21:00'), 90),
    'Brian': ('Russian Hill', time_to_minutes('15:30'), time_to_minutes('21:45'), 60),
    'Kenneth': ('North Beach', time_to_minutes('9:45'), time_to_minutes('21:00'), 30),
    'Jason': ('Chinatown', time_to_minutes('8:15'), time_to_minutes('11:45'), 75),
    'Stephanie': ('Union Square', time_to_minutes('14:45'), time_to_minutes('18:45'), 105),
    'Kimberly': ('Embarcadero', time_to_minutes('9:45'), time_to_minutes('19:30'), 75),
    'Steven': ('Financial District', time_to_minutes('7:15'), time_to_minutes('21:15'), 60),
    'Mark': ('Marina District', time_to_minutes('10:15'), time_to_minutes('13:00'), 75)
}

# Filter friends we can possibly meet (duration fits in their window)
possible_friends = {name: data for name, data in friends.items() if data[3] <= (data[2] - data[1])}

# Generate all possible meeting orders (permutations)
def generate_schedules():
    # We'll try all possible orders of meeting friends, but limit to 4 friends max for performance
    for count in range(1, len(possible_friends)+1):
        for friend_order in permutations(possible_friends.keys(), count):
            yield friend_order

def evaluate_schedule(friend_order):
    current_time = time_to_minutes('9:00')  # Start at Presidio at 9:00
    current_location = 'Presidio'
    schedule = []
    total_meetings = 0
    
    for friend in friend_order:
        location, avail_start, avail_end, duration = possible_friends[friend]
        
        # Calculate travel time
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        # Can we arrive before their window ends?
        if arrival_time >= avail_end:
            continue  # Can't meet this friend
        
        # Calculate meeting start time
        meeting_start = max(arrival_time, avail_start)
        meeting_end = meeting_start + duration
        
        # Can we complete the meeting before their window ends?
        if meeting_end > avail_end:
            continue  # Can't meet this friend
        
        # Add to schedule
        schedule.append({
            'friend': friend,
            'location': location,
            'start': meeting_start,
            'end': meeting_end,
            'travel_time': travel_time
        })
        
        current_time = meeting_end
        current_location = location
        total_meetings += 1
    
    return total_meetings, schedule

# Find the best schedule
best_meetings = 0
best_schedule = []

# We'll limit the permutations to reasonable numbers for performance
max_attempts = 1000
attempts = 0

for friend_order in generate_schedules():
    attempts += 1
    if attempts > max_attempts:
        break
    
    total_meetings, schedule = evaluate_schedule(friend_order)
    
    if total_meetings > best_meetings:
        best_meetings = total_meetings
        best_schedule = schedule
    elif total_meetings == best_meetings and len(schedule) > 0:
        # Prefer schedules that end earlier
        if schedule[-1]['end'] < best_schedule[-1]['end']:
            best_schedule = schedule

# Convert to output format
itinerary = []
for meeting in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": meeting['location'],
        "person": meeting['friend'],
        "start_time": minutes_to_time(meeting['start']),
        "end_time": minutes_to_time(meeting['end'])
    })

# Output the result
result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=2))