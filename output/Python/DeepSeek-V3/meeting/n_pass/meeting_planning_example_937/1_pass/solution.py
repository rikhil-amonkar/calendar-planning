import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input data
travel_times = {
    'Russian Hill': {
        'Sunset District': 23,
        'Union Square': 10,
        'Nob Hill': 5,
        'Marina District': 7,
        'Richmond District': 14,
        'Financial District': 11,
        'Embarcadero': 8,
        'The Castro': 21,
        'Alamo Square': 15,
        'Presidio': 14
    },
    'Sunset District': {
        'Russian Hill': 24,
        'Union Square': 30,
        'Nob Hill': 27,
        'Marina District': 21,
        'Richmond District': 12,
        'Financial District': 30,
        'Embarcadero': 30,
        'The Castro': 17,
        'Alamo Square': 17,
        'Presidio': 16
    },
    'Union Square': {
        'Russian Hill': 13,
        'Sunset District': 27,
        'Nob Hill': 9,
        'Marina District': 18,
        'Richmond District': 20,
        'Financial District': 9,
        'Embarcadero': 11,
        'The Castro': 17,
        'Alamo Square': 15,
        'Presidio': 24
    },
    'Nob Hill': {
        'Russian Hill': 5,
        'Sunset District': 24,
        'Union Square': 7,
        'Marina District': 11,
        'Richmond District': 14,
        'Financial District': 9,
        'Embarcadero': 9,
        'The Castro': 17,
        'Alamo Square': 11,
        'Presidio': 17
    },
    'Marina District': {
        'Russian Hill': 8,
        'Sunset District': 19,
        'Union Square': 16,
        'Nob Hill': 12,
        'Richmond District': 11,
        'Financial District': 17,
        'Embarcadero': 14,
        'The Castro': 22,
        'Alamo Square': 15,
        'Presidio': 10
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Sunset District': 11,
        'Union Square': 21,
        'Nob Hill': 17,
        'Marina District': 9,
        'Financial District': 22,
        'Embarcadero': 19,
        'The Castro': 16,
        'Alamo Square': 13,
        'Presidio': 7
    },
    'Financial District': {
        'Russian Hill': 11,
        'Sunset District': 30,
        'Union Square': 9,
        'Nob Hill': 8,
        'Marina District': 15,
        'Richmond District': 21,
        'Embarcadero': 4,
        'The Castro': 20,
        'Alamo Square': 17,
        'Presidio': 22
    },
    'Embarcadero': {
        'Russian Hill': 8,
        'Sunset District': 30,
        'Union Square': 10,
        'Nob Hill': 10,
        'Marina District': 12,
        'Richmond District': 21,
        'Financial District': 5,
        'The Castro': 25,
        'Alamo Square': 19,
        'Presidio': 20
    },
    'The Castro': {
        'Russian Hill': 18,
        'Sunset District': 17,
        'Union Square': 19,
        'Nob Hill': 16,
        'Marina District': 21,
        'Richmond District': 16,
        'Financial District': 21,
        'Embarcadero': 22,
        'Alamo Square': 8,
        'Presidio': 20
    },
    'Alamo Square': {
        'Russian Hill': 13,
        'Sunset District': 16,
        'Union Square': 14,
        'Nob Hill': 11,
        'Marina District': 15,
        'Richmond District': 11,
        'Financial District': 17,
        'Embarcadero': 16,
        'The Castro': 8,
        'Presidio': 17
    },
    'Presidio': {
        'Russian Hill': 14,
        'Sunset District': 15,
        'Union Square': 22,
        'Nob Hill': 18,
        'Marina District': 11,
        'Richmond District': 7,
        'Financial District': 23,
        'Embarcadero': 20,
        'The Castro': 21,
        'Alamo Square': 19
    }
}

friends = {
    'David': {
        'location': 'Sunset District',
        'start': '9:15',
        'end': '22:00',
        'duration': 15
    },
    'Kenneth': {
        'location': 'Union Square',
        'start': '21:15',
        'end': '21:45',
        'duration': 15
    },
    'Patricia': {
        'location': 'Nob Hill',
        'start': '15:00',
        'end': '19:15',
        'duration': 120
    },
    'Mary': {
        'location': 'Marina District',
        'start': '14:45',
        'end': '16:45',
        'duration': 45
    },
    'Charles': {
        'location': 'Richmond District',
        'start': '17:15',
        'end': '21:00',
        'duration': 15
    },
    'Joshua': {
        'location': 'Financial District',
        'start': '14:30',
        'end': '17:15',
        'duration': 90
    },
    'Ronald': {
        'location': 'Embarcadero',
        'start': '18:15',
        'end': '20:45',
        'duration': 30
    },
    'George': {
        'location': 'The Castro',
        'start': '14:15',
        'end': '19:00',
        'duration': 105
    },
    'Kimberly': {
        'location': 'Alamo Square',
        'start': '9:00',
        'end': '14:30',
        'duration': 105
    },
    'William': {
        'location': 'Presidio',
        'start': '7:00',
        'end': '12:45',
        'duration': 60
    }
}

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    return travel_times[from_loc][to_loc]

def is_schedule_valid(schedule):
    current_time = time_to_minutes('9:00')
    current_location = 'Russian Hill'
    
    for entry in schedule:
        friend = entry['person']
        friend_data = friends[friend]
        location = friend_data['location']
        
        # Travel to location
        travel_time = get_travel_time(current_location, location)
        current_time += travel_time
        current_location = location
        
        # Check if we can meet within friend's availability
        start_time = max(current_time, time_to_minutes(friend_data['start']))
        end_time = min(start_time + friend_data['duration'], time_to_minutes(friend_data['end']))
        
        if end_time - start_time < friend_data['duration']:
            return False
        
        current_time = end_time
    
    return True

def generate_itinerary(schedule):
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Russian Hill'
    
    for entry in schedule:
        friend = entry['person']
        friend_data = friends[friend]
        location = friend_data['location']
        
        # Travel to location
        travel_time = get_travel_time(current_location, location)
        current_time += travel_time
        current_location = location
        
        # Meeting time
        start_time = max(current_time, time_to_minutes(friend_data['start']))
        end_time = start_time + friend_data['duration']
        current_time = end_time
        
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': friend,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
    
    return itinerary

def main():
    friend_names = list(friends.keys())
    best_schedule = None
    
    # Try different orders to find a valid schedule
    for order in permutations(friend_names):
        schedule = [{'person': name} for name in order]
        if is_schedule_valid(schedule):
            best_schedule = schedule
            break
    
    if best_schedule:
        itinerary = generate_itinerary(best_schedule)
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print(json.dumps({'itinerary': []}, indent=2))

if __name__ == '__main__':
    main()