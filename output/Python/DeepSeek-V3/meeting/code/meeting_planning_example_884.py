import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Richmond District': {
        'Chinatown': 20,
        'Sunset District': 11,
        'Alamo Square': 13,
        'Financial District': 22,
        'North Beach': 17,
        'Embarcadero': 19,
        'Presidio': 7,
        'Golden Gate Park': 9,
        'Bayview': 27
    },
    'Chinatown': {
        'Richmond District': 20,
        'Sunset District': 29,
        'Alamo Square': 17,
        'Financial District': 5,
        'North Beach': 3,
        'Embarcadero': 5,
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 20
    },
    'Sunset District': {
        'Richmond District': 12,
        'Chinatown': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'North Beach': 28,
        'Embarcadero': 30,
        'Presidio': 16,
        'Golden Gate Park': 11,
        'Bayview': 22
    },
    'Alamo Square': {
        'Richmond District': 11,
        'Chinatown': 15,
        'Sunset District': 16,
        'Financial District': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Presidio': 17,
        'Golden Gate Park': 9,
        'Bayview': 16
    },
    'Financial District': {
        'Richmond District': 21,
        'Chinatown': 5,
        'Sunset District': 30,
        'Alamo Square': 17,
        'North Beach': 7,
        'Embarcadero': 4,
        'Presidio': 22,
        'Golden Gate Park': 23,
        'Bayview': 19
    },
    'North Beach': {
        'Richmond District': 18,
        'Chinatown': 6,
        'Sunset District': 27,
        'Alamo Square': 16,
        'Financial District': 8,
        'Embarcadero': 6,
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 25
    },
    'Embarcadero': {
        'Richmond District': 21,
        'Chinatown': 7,
        'Sunset District': 30,
        'Alamo Square': 19,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20,
        'Golden Gate Park': 25,
        'Bayview': 21
    },
    'Presidio': {
        'Richmond District': 7,
        'Chinatown': 21,
        'Sunset District': 15,
        'Alamo Square': 19,
        'Financial District': 23,
        'North Beach': 18,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Bayview': 31
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Chinatown': 23,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'North Beach': 23,
        'Embarcadero': 25,
        'Presidio': 11,
        'Bayview': 23
    },
    'Bayview': {
        'Richmond District': 25,
        'Chinatown': 19,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'North Beach': 22,
        'Embarcadero': 19,
        'Presidio': 32,
        'Golden Gate Park': 22
    }
}

# Friend data: name -> (location, available_start, available_end, min_duration)
friends = {
    'Robert': ('Chinatown', 7.75, 17.5, 120),
    'David': ('Sunset District', 12.5, 19.75, 45),
    'Matthew': ('Alamo Square', 8.75, 13.75, 90),
    'Jessica': ('Financial District', 9.5, 18.75, 45),
    'Melissa': ('North Beach', 7.25, 16.75, 45),
    'Mark': ('Embarcadero', 15.25, 17.0, 45),
    'Deborah': ('Presidio', 19.0, 19.75, 45),
    'Karen': ('Golden Gate Park', 19.5, 22.0, 120),
    'Laura': ('Bayview', 21.25, 22.25, 15)
}

def time_to_float(time_str):
    if isinstance(time_str, float):
        return time_str
    h, m = map(int, time_str.split(':'))
    return h + m / 60.0

def float_to_time(time_float):
    h = int(time_float)
    m = int((time_float - h) * 60)
    return f"{h}:{m:02d}"

def calculate_schedule(order):
    current_time = 9.0  # Starting at 9:00 AM in Richmond District
    current_location = 'Richmond District'
    schedule = []
    met_friends = set()
    
    for friend in order:
        name = friend
        location, avail_start, avail_end, min_duration = friends[friend]
        
        # Travel to friend's location
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time / 60.0
        
        # Calculate meeting window
        meeting_start = max(arrival_time, avail_start)
        meeting_end = min(meeting_start + min_duration / 60.0, avail_end)
        
        if meeting_end - meeting_start >= min_duration / 60.0:
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': name,
                'start_time': float_to_time(meeting_start),
                'end_time': float_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = location
            met_friends.add(friend)
        else:
            return None, 0
    
    # Check if we can meet Deborah and Karen
    # Try to meet Deborah
    deborah_loc, deborah_start, deborah_end, deborah_dur = friends['Deborah']
    travel_time = travel_times[current_location][deborah_loc]
    arrival_time = current_time + travel_time / 60.0
    meeting_start = max(arrival_time, deborah_start)
    meeting_end = min(meeting_start + deborah_dur / 60.0, deborah_end)
    
    if meeting_end - meeting_start >= deborah_dur / 60.0:
        schedule.append({
            'action': 'meet',
            'location': deborah_loc,
            'person': 'Deborah',
            'start_time': float_to_time(meeting_start),
            'end_time': float_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = deborah_loc
        met_friends.add('Deborah')
    
    # Try to meet Karen
    karen_loc, karen_start, karen_end, karen_dur = friends['Karen']
    travel_time = travel_times[current_location][karen_loc]
    arrival_time = current_time + travel_time / 60.0
    meeting_start = max(arrival_time, karen_start)
    meeting_end = min(meeting_start + karen_dur / 60.0, karen_end)
    
    if meeting_end - meeting_start >= karen_dur / 60.0:
        schedule.append({
            'action': 'meet',
            'location': karen_loc,
            'person': 'Karen',
            'start_time': float_to_time(meeting_start),
            'end_time': float_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = karen_loc
        met_friends.add('Karen')
    
    # Try to meet Laura
    laura_loc, laura_start, laura_end, laura_dur = friends['Laura']
    travel_time = travel_times[current_location][laura_loc]
    arrival_time = current_time + travel_time / 60.0
    meeting_start = max(arrival_time, laura_start)
    meeting_end = min(meeting_start + laura_dur / 60.0, laura_end)
    
    if meeting_end - meeting_start >= laura_dur / 60.0:
        schedule.append({
            'action': 'meet',
            'location': laura_loc,
            'person': 'Laura',
            'start_time': float_to_time(meeting_start),
            'end_time': float_to_time(meeting_end)
        })
        met_friends.add('Laura')
    
    return schedule, len(met_friends)

def find_optimal_schedule():
    best_schedule = None
    best_count = 0
    friends_to_schedule = ['Robert', 'David', 'Matthew', 'Jessica', 'Melissa', 'Mark']
    
    # Try all permutations of the first 6 friends (since the others have very specific times)
    for perm in permutations(friends_to_schedule):
        schedule, count = calculate_schedule(perm)
        if schedule and count > best_count:
            best_schedule = schedule
            best_count = count
    
    return best_schedule

optimal_schedule = find_optimal_schedule()
output = {"itinerary": optimal_schedule} if optimal_schedule else {"itinerary": []}
print(json.dumps(output, indent=2))