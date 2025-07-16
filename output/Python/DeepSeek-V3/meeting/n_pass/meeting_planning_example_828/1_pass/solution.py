import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Marina District': {
        'Richmond District': 11,
        'Union Square': 16,
        'Nob Hill': 12,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 18,
        'Embarcadero': 14,
        'Financial District': 17,
        'North Beach': 11,
        'Presidio': 10
    },
    'Richmond District': {
        'Marina District': 9,
        'Union Square': 21,
        'Nob Hill': 17,
        'Fisherman\'s Wharf': 18,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Financial District': 22,
        'North Beach': 17,
        'Presidio': 7
    },
    'Union Square': {
        'Marina District': 18,
        'Richmond District': 20,
        'Nob Hill': 9,
        'Fisherman\'s Wharf': 15,
        'Golden Gate Park': 22,
        'Embarcadero': 11,
        'Financial District': 9,
        'North Beach': 10,
        'Presidio': 24
    },
    'Nob Hill': {
        'Marina District': 11,
        'Richmond District': 14,
        'Union Square': 7,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Financial District': 9,
        'North Beach': 8,
        'Presidio': 17
    },
    'Fisherman\'s Wharf': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 13,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Financial District': 11,
        'North Beach': 6,
        'Presidio': 17
    },
    'Golden Gate Park': {
        'Marina District': 16,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 20,
        'Fisherman\'s Wharf': 24,
        'Embarcadero': 25,
        'Financial District': 26,
        'North Beach': 23,
        'Presidio': 11
    },
    'Embarcadero': {
        'Marina District': 12,
        'Richmond District': 21,
        'Union Square': 10,
        'Nob Hill': 10,
        'Fisherman\'s Wharf': 6,
        'Golden Gate Park': 25,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20
    },
    'Financial District': {
        'Marina District': 15,
        'Richmond District': 21,
        'Union Square': 9,
        'Nob Hill': 8,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 23,
        'Embarcadero': 4,
        'North Beach': 7,
        'Presidio': 22
    },
    'North Beach': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 7,
        'Nob Hill': 7,
        'Fisherman\'s Wharf': 5,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Financial District': 8,
        'Presidio': 17
    },
    'Presidio': {
        'Marina District': 11,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 18,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 12,
        'Embarcadero': 20,
        'Financial District': 23,
        'North Beach': 18
    }
}

# Friend availability
friends = {
    'Stephanie': {
        'location': 'Richmond District',
        'start': 16.25,  # 4:15 PM
        'end': 21.5,     # 9:30 PM
        'duration': 1.25  # 75 minutes
    },
    'William': {
        'location': 'Union Square',
        'start': 10.75,  # 10:45 AM
        'end': 17.5,     # 5:30 PM
        'duration': 0.75  # 45 minutes
    },
    'Elizabeth': {
        'location': 'Nob Hill',
        'start': 12.25,  # 12:15 PM
        'end': 15.0,     # 3:00 PM
        'duration': 1.75  # 105 minutes
    },
    'Joseph': {
        'location': 'Fisherman\'s Wharf',
        'start': 12.75,  # 12:45 PM
        'end': 14.0,     # 2:00 PM
        'duration': 1.25  # 75 minutes
    },
    'Anthony': {
        'location': 'Golden Gate Park',
        'start': 13.0,   # 1:00 PM
        'end': 20.5,     # 8:30 PM
        'duration': 1.25  # 75 minutes
    },
    'Barbara': {
        'location': 'Embarcadero',
        'start': 19.25,  # 7:15 PM
        'end': 20.5,     # 8:30 PM
        'duration': 1.25  # 75 minutes
    },
    'Carol': {
        'location': 'Financial District',
        'start': 11.75,  # 11:45 AM
        'end': 16.25,   # 4:15 PM
        'duration': 1.0  # 60 minutes
    },
    'Sandra': {
        'location': 'North Beach',
        'start': 10.0,  # 10:00 AM
        'end': 12.5,    # 12:30 PM
        'duration': 0.25  # 15 minutes
    },
    'Kenneth': {
        'location': 'Presidio',
        'start': 21.25,  # 9:15 PM
        'end': 22.25,   # 10:15 PM
        'duration': 0.75  # 45 minutes
    }
}

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    try:
        return travel_times[from_loc][to_loc] / 60.0
    except KeyError:
        return travel_times[to_loc][from_loc] / 60.0

def is_schedule_valid(schedule):
    current_time = 9.0  # Start at 9:00 AM at Marina District
    current_location = 'Marina District'
    
    for meeting in schedule:
        # Travel to meeting location
        travel_time = get_travel_time(current_location, meeting['location'])
        arrival_time = current_time + travel_time
        
        # Check if we arrive before meeting window ends
        if arrival_time > friends[meeting['person']]['end']:
            return False
        
        # Start meeting as soon as possible after arrival
        start_time = max(arrival_time, friends[meeting['person']]['start'])
        end_time = start_time + friends[meeting['person']]['duration']
        
        # Check if meeting fits in window
        if end_time > friends[meeting['person']]['end']:
            return False
        
        # Update current time and location
        current_time = end_time
        current_location = meeting['location']
    
    return True

def calculate_schedule_score(schedule):
    if not is_schedule_valid(schedule):
        return 0
    
    # Count number of friends met
    return len(schedule)

def generate_best_schedule():
    friend_names = list(friends.keys())
    best_schedule = []
    best_score = 0
    
    # Try all possible orders (limited to 5 friends due to computational constraints)
    for perm in permutations(friend_names, min(5, len(friend_names))):
        schedule = [{'person': name, 'location': friends[name]['location']} for name in perm]
        score = calculate_schedule_score(schedule)
        
        if score > best_score:
            best_score = score
            best_schedule = schedule
    
    return best_schedule

def build_itinerary(schedule):
    if not schedule:
        return {"itinerary": []}
    
    itinerary = []
    current_time = 9.0  # Start at 9:00 AM at Marina District
    current_location = 'Marina District'
    
    for meeting in schedule:
        # Travel to meeting location
        travel_time = get_travel_time(current_location, meeting['location'])
        arrival_time = current_time + travel_time
        
        # Add travel action if needed
        if travel_time > 0:
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": meeting['location'],
                "start_time": float_to_time(current_time),
                "end_time": float_to_time(arrival_time)
            })
        
        # Calculate meeting times
        start_time = max(arrival_time, friends[meeting['person']]['start'])
        end_time = start_time + friends[meeting['person']]['duration']
        
        # Add meeting action
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": float_to_time(start_time),
            "end_time": float_to_time(end_time)
        })
        
        # Update current time and location
        current_time = end_time
        current_location = meeting['location']
    
    return {"itinerary": itinerary}

# Generate and output the best schedule
best_schedule = generate_best_schedule()
result = build_itinerary(best_schedule)
print(json.dumps(result, indent=2))