import json
from itertools import permutations

# Complete travel times between all locations in minutes
travel_times = {
    'Mission District': {
        'Alamo Square': 15,
        'Presidio': 25,
        'Russian Hill': 20,
        'North Beach': 15,
        'Golden Gate Park': 20,
        'Richmond District': 25,
        'Embarcadero': 10,
        'Financial District': 10,
        'Marina District': 20
    },
    'Alamo Square': {
        'Mission District': 15,
        'Presidio': 20,
        'Russian Hill': 10,
        'North Beach': 15,
        'Golden Gate Park': 25,
        'Richmond District': 15,
        'Embarcadero': 20,
        'Financial District': 15,
        'Marina District': 15
    },
    'Presidio': {
        'Mission District': 25,
        'Alamo Square': 20,
        'Russian Hill': 15,
        'North Beach': 20,
        'Golden Gate Park': 15,
        'Richmond District': 10,
        'Embarcadero': 25,
        'Financial District': 20,
        'Marina District': 10
    },
    'Russian Hill': {
        'Mission District': 20,
        'Alamo Square': 10,
        'Presidio': 15,
        'North Beach': 5,
        'Golden Gate Park': 20,
        'Richmond District': 15,
        'Embarcadero': 15,
        'Financial District': 10,
        'Marina District': 10
    },
    'North Beach': {
        'Mission District': 15,
        'Alamo Square': 15,
        'Presidio': 20,
        'Russian Hill': 5,
        'Golden Gate Park': 25,
        'Richmond District': 20,
        'Embarcadero': 10,
        'Financial District': 5,
        'Marina District': 15
    },
    'Golden Gate Park': {
        'Mission District': 20,
        'Alamo Square': 25,
        'Presidio': 15,
        'Russian Hill': 20,
        'North Beach': 25,
        'Richmond District': 10,
        'Embarcadero': 30,
        'Financial District': 25,
        'Marina District': 20
    },
    'Richmond District': {
        'Mission District': 25,
        'Alamo Square': 15,
        'Presidio': 10,
        'Russian Hill': 15,
        'North Beach': 20,
        'Golden Gate Park': 10,
        'Embarcadero': 25,
        'Financial District': 20,
        'Marina District': 15
    },
    'Embarcadero': {
        'Mission District': 10,
        'Alamo Square': 20,
        'Presidio': 25,
        'Russian Hill': 15,
        'North Beach': 10,
        'Golden Gate Park': 30,
        'Richmond District': 25,
        'Financial District': 5,
        'Marina District': 15
    },
    'Financial District': {
        'Mission District': 10,
        'Alamo Square': 15,
        'Presidio': 20,
        'Russian Hill': 10,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Richmond District': 20,
        'Embarcadero': 5,
        'Marina District': 10
    },
    'Marina District': {
        'Mission District': 20,
        'Alamo Square': 15,
        'Presidio': 10,
        'Russian Hill': 10,
        'North Beach': 15,
        'Golden Gate Park': 20,
        'Richmond District': 15,
        'Embarcadero': 15,
        'Financial District': 10
    }
}

# Friend constraints with correct time windows
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
    if from_loc == to_loc:
        return 0
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
        
        # Check if we can arrive in time for meeting
        latest_start = meeting_end - min_duration
        if arrival_time > latest_start:
            return False
        
        # Calculate meeting time
        start_time = max(arrival_time, meeting_start)
        end_time = start_time + min_duration
        
        # Update current time and location
        current_time = end_time
        current_location = meeting['location']
    
    return True

def calculate_score(schedule):
    if not is_schedule_valid(schedule):
        return -1
    
    # Count number of friends met and total time spent
    total_time = 0
    for meeting in schedule:
        total_time += meeting['min_duration']
    return len(schedule) * 1000 + total_time  # Prioritize more meetings, then duration

def generate_schedule():
    best_schedule = []
    best_score = 0
    
    # Try all possible orders (limited to 5 friends for performance)
    for friend_subset in permutations(friends, 5):
        # Try to build a schedule with these friends in this order
        current_schedule = []
        current_time = time_to_minutes('9:00')
        current_location = 'Mission District'
        
        for friend in friend_subset:
            # Calculate travel time
            travel_time = get_travel_time(current_location, friend['location'])
            arrival_time = current_time + travel_time
            
            # Calculate possible meeting window
            meeting_start = time_to_minutes(friend['start'])
            meeting_end = time_to_minutes(friend['end'])
            min_duration = friend['min_duration']
            
            latest_start = meeting_end - min_duration
            if arrival_time > latest_start:
                continue  # Can't make this meeting
            
            start_time = max(arrival_time, meeting_start)
            end_time = start_time + min_duration
            
            # Add to schedule
            current_schedule.append(friend)
            current_time = end_time
            current_location = friend['location']
        
        # Evaluate this schedule
        current_score = calculate_score(current_schedule)
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
        end_time = start_time + min_duration
        
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