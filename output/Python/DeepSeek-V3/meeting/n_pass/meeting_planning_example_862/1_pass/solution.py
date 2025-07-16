import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Mission District': {
        'Alamo Square': 11,
        'Presidio': 25,
        'Russian Hill': 15,
        'North Beach': 17,
        'Golden Gate Park': 17,
        'Richmond District': 20,
        'Embarcadero': 19,
        'Financial District': 15,
        'Marina District': 19
    },
    'Alamo Square': {
        'Mission District': 10,
        'Presidio': 17,
        'Russian Hill': 13,
        'North Beach': 15,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Embarcadero': 16,
        'Financial District': 17,
        'Marina District': 15
    },
    'Presidio': {
        'Mission District': 26,
        'Alamo Square': 19,
        'Russian Hill': 14,
        'North Beach': 18,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Embarcadero': 20,
        'Financial District': 23,
        'Marina District': 11
    },
    'Russian Hill': {
        'Mission District': 16,
        'Alamo Square': 15,
        'Presidio': 14,
        'North Beach': 5,
        'Golden Gate Park': 21,
        'Richmond District': 14,
        'Embarcadero': 8,
        'Financial District': 11,
        'Marina District': 7
    },
    'North Beach': {
        'Mission District': 18,
        'Alamo Square': 16,
        'Presidio': 17,
        'Russian Hill': 4,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Embarcadero': 6,
        'Financial District': 8,
        'Marina District': 9
    },
    'Golden Gate Park': {
        'Mission District': 17,
        'Alamo Square': 9,
        'Presidio': 11,
        'Russian Hill': 19,
        'North Beach': 23,
        'Richmond District': 7,
        'Embarcadero': 25,
        'Financial District': 26,
        'Marina District': 16
    },
    'Richmond District': {
        'Mission District': 20,
        'Alamo Square': 13,
        'Presidio': 7,
        'Russian Hill': 13,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Financial District': 22,
        'Marina District': 9
    },
    'Embarcadero': {
        'Mission District': 20,
        'Alamo Square': 19,
        'Presidio': 20,
        'Russian Hill': 8,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Financial District': 5,
        'Marina District': 12
    },
    'Financial District': {
        'Mission District': 17,
        'Alamo Square': 17,
        'Presidio': 22,
        'Russian Hill': 11,
        'North Beach': 7,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Embarcadero': 4,
        'Marina District': 17
    },
    'Marina District': {
        'Mission District': 20,
        'Alamo Square': 15,
        'Presidio': 10,
        'Russian Hill': 8,
        'North Beach': 11,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Embarcadero': 14,
        'Financial District': 17
    }
}

# Friend constraints
friends = [
    {'name': 'Laura', 'location': 'Alamo Square', 'start': '14:30', 'end': '16:15', 'min_duration': 75},
    {'name': 'Brian', 'location': 'Presidio', 'start': '10:15', 'end': '17:00', 'min_duration': 30},
    {'name': 'Karen', 'location': 'Russian Hill', 'start': '18:00', 'end': '20:15', 'min_duration': 90},
    {'name': 'Stephanie', 'location': 'North Beach', 'start': '10:15', 'end': '16:00', 'min_duration': 75},
    {'name': 'Helen', 'location': 'Golden Gate Park', 'start': '11:30', 'end': '21:45', 'min_duration': 120},
    {'name': 'Sandra', 'location': 'Richmond District', 'start': '8:00', 'end': '15:15', 'min_duration': 30},
    {'name': 'Mary', 'location': 'Embarcadero', 'start': '16:45', 'end': '18:45', 'min_duration': 120},
    {'name': 'Deborah', 'location': 'Financial District', 'start': '19:00', 'end': '20:45', 'min_duration': 105},
    {'name': 'Elizabeth', 'location': 'Marina District', 'start': '8:30', 'end': '13:15', 'min_duration': 105}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times.get(from_loc, {}).get(to_loc, float('inf'))

def is_schedule_valid(schedule):
    current_time = time_to_minutes('9:00')
    current_location = 'Mission District'
    
    for meeting in schedule:
        # Travel to meeting location
        travel_time = get_travel_time(current_location, meeting['location'])
        if travel_time == float('inf'):
            return False
        
        arrival_time = current_time + travel_time
        meeting_start = time_to_minutes(meeting['start'])
        meeting_end = time_to_minutes(meeting['end'])
        min_duration = meeting['min_duration']
        
        # Check if we can arrive on time and meet for required duration
        if arrival_time > meeting_start:
            return False
        
        actual_duration = min(meeting_end - arrival_time, meeting_end - meeting_start)
        if actual_duration < min_duration:
            return False
        
        # Update current time and location
        current_time = arrival_time + actual_duration
        current_location = meeting['location']
    
    return True

def calculate_score(schedule):
    if not is_schedule_valid(schedule):
        return -1
    
    # Count number of friends met
    return len(schedule)

def generate_schedule():
    best_schedule = []
    best_score = 0
    
    # Try all possible orders (limited to 5 friends due to computational constraints)
    for friend_subset in permutations(friends, 5):
        current_schedule = []
        current_score = 0
        
        for friend in friend_subset:
            temp_schedule = current_schedule + [friend]
            if is_schedule_valid(temp_schedule):
                current_schedule = temp_schedule
                current_score += 1
        
        if current_score > best_score:
            best_score = current_score
            best_schedule = current_schedule
    
    return best_schedule

def format_schedule(schedule):
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Mission District'
    
    for meeting in schedule:
        # Travel to meeting location
        travel_time = get_travel_time(current_location, meeting['location'])
        arrival_time = current_time + travel_time
        meeting_start = time_to_minutes(meeting['start'])
        meeting_end = time_to_minutes(meeting['end'])
        min_duration = meeting['min_duration']
        
        # Calculate meeting time
        start_time = max(arrival_time, meeting_start)
        end_time = min(meeting_end, start_time + min_duration)
        
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['name'],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = meeting['location']
    
    return {"itinerary": itinerary}

# Generate and output the schedule
schedule = generate_schedule()
result = format_schedule(schedule)
print(json.dumps(result, indent=2))