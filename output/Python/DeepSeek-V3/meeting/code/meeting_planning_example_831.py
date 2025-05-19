import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Presidio': {
        'Fisherman\'s Wharf': 19,
        'Alamo Square': 19,
        'Financial District': 23,
        'Union Square': 22,
        'Sunset District': 15,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Chinatown': 21,
        'Richmond District': 7
    },
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Alamo Square': 21,
        'Financial District': 11,
        'Union Square': 13,
        'Sunset District': 27,
        'Embarcadero': 8,
        'Golden Gate Park': 25,
        'Chinatown': 12,
        'Richmond District': 18
    },
    'Alamo Square': {
        'Presidio': 17,
        'Fisherman\'s Wharf': 19,
        'Financial District': 17,
        'Union Square': 14,
        'Sunset District': 16,
        'Embarcadero': 16,
        'Golden Gate Park': 9,
        'Chinatown': 15,
        'Richmond District': 11
    },
    'Financial District': {
        'Presidio': 22,
        'Fisherman\'s Wharf': 10,
        'Alamo Square': 17,
        'Union Square': 9,
        'Sunset District': 30,
        'Embarcadero': 4,
        'Golden Gate Park': 23,
        'Chinatown': 5,
        'Richmond District': 21
    },
    'Union Square': {
        'Presidio': 24,
        'Fisherman\'s Wharf': 15,
        'Alamo Square': 15,
        'Financial District': 9,
        'Sunset District': 27,
        'Embarcadero': 11,
        'Golden Gate Park': 22,
        'Chinatown': 7,
        'Richmond District': 20
    },
    'Sunset District': {
        'Presidio': 16,
        'Fisherman\'s Wharf': 29,
        'Alamo Square': 17,
        'Financial District': 30,
        'Union Square': 30,
        'Embarcadero': 30,
        'Golden Gate Park': 11,
        'Chinatown': 30,
        'Richmond District': 12
    },
    'Embarcadero': {
        'Presidio': 20,
        'Fisherman\'s Wharf': 6,
        'Alamo Square': 19,
        'Financial District': 5,
        'Union Square': 10,
        'Sunset District': 30,
        'Golden Gate Park': 25,
        'Chinatown': 7,
        'Richmond District': 21
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Fisherman\'s Wharf': 24,
        'Alamo Square': 9,
        'Financial District': 26,
        'Union Square': 22,
        'Sunset District': 10,
        'Embarcadero': 25,
        'Chinatown': 23,
        'Richmond District': 7
    },
    'Chinatown': {
        'Presidio': 19,
        'Fisherman\'s Wharf': 8,
        'Alamo Square': 17,
        'Financial District': 5,
        'Union Square': 7,
        'Sunset District': 29,
        'Embarcadero': 5,
        'Golden Gate Park': 23,
        'Richmond District': 20
    },
    'Richmond District': {
        'Presidio': 7,
        'Fisherman\'s Wharf': 18,
        'Alamo Square': 13,
        'Financial District': 22,
        'Union Square': 21,
        'Sunset District': 11,
        'Embarcadero': 19,
        'Golden Gate Park': 9,
        'Chinatown': 20
    }
}

# Friend data: name -> (location, start, end, min_duration)
friends = {
    'Jeffrey': ('Fisherman\'s Wharf', '10:15', '13:00', 90),
    'Ronald': ('Alamo Square', '7:45', '14:45', 120),
    'Jason': ('Financial District', '10:45', '16:00', 105),
    'Melissa': ('Union Square', '17:45', '18:15', 15),
    'Elizabeth': ('Sunset District', '14:45', '17:30', 105),
    'Margaret': ('Embarcadero', '13:15', '19:00', 90),
    'George': ('Golden Gate Park', '19:00', '22:00', 75),
    'Richard': ('Chinatown', '9:30', '21:00', 15),
    'Laura': ('Richmond District', '9:45', '18:00', 60)
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule(order):
    current_location = 'Presidio'
    current_time = time_to_minutes('9:00')
    schedule = []
    met_friends = set()
    
    for friend in order:
        name = friend
        location, start_str, end_str, min_duration = friends[friend]
        start = time_to_minutes(start_str)
        end = time_to_minutes(end_str)
        
        # Travel to location
        travel_time = travel_times[current_location].get(location, float('inf'))
        arrival_time = current_time + travel_time
        
        # Calculate meeting window
        meeting_start = max(arrival_time, start)
        meeting_end = min(meeting_start + min_duration, end)
        
        if meeting_end - meeting_start >= min_duration:
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': name,
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            met_friends.add(name)
            current_time = meeting_end
            current_location = location
    
    # Add George at the end if not already met
    if 'George' not in met_friends:
        location, start_str, end_str, min_duration = friends['George']
        travel_time = travel_times[current_location].get(location, float('inf'))
        arrival_time = current_time + travel_time
        start = time_to_minutes(start_str)
        end = time_to_minutes(end_str)
        
        meeting_start = max(arrival_time, start)
        meeting_end = min(meeting_start + min_duration, end)
        
        if meeting_end - meeting_start >= min_duration:
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': 'George',
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            met_friends.add('George')
    
    return schedule, len(met_friends)

def find_optimal_schedule():
    friend_names = [name for name in friends if name != 'George']
    best_schedule = []
    max_met = 0
    
    # Try all permutations of 5 friends (to keep computation reasonable)
    from itertools import combinations
    for friends_subset in combinations(friend_names, 5):
        for order in permutations(friends_subset):
            schedule, num_met = calculate_schedule(order)
            if num_met > max_met or (num_met == max_met and len(schedule) > len(best_schedule)):
                max_met = num_met
                best_schedule = schedule
    
    return best_schedule

optimal_schedule = find_optimal_schedule()
result = {
    "itinerary": optimal_schedule
}

print(json.dumps(result, indent=2))