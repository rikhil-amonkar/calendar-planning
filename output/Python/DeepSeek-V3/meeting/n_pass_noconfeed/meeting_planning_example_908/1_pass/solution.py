import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (from_location, to_location): time
travel_times = {
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Sunset District'): 23,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Sunset District'): 11,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Sunset District'): 27,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Union Square'): 30
}

# Friend constraints
friends = [
    {
        'name': 'Mark',
        'location': 'Fisherman\'s Wharf',
        'available_start': '8:15',
        'available_end': '10:00',
        'duration': 30
    },
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'available_start': '12:15',
        'available_end': '15:00',
        'duration': 75
    },
    {
        'name': 'Betty',
        'location': 'Bayview',
        'available_start': '7:15',
        'available_end': '20:30',
        'duration': 15
    },
    {
        'name': 'Lisa',
        'location': 'Haight-Ashbury',
        'available_start': '15:30',
        'available_end': '18:30',
        'duration': 45
    },
    {
        'name': 'William',
        'location': 'Russian Hill',
        'available_start': '18:45',
        'available_end': '20:00',
        'duration': 60
    },
    {
        'name': 'Brian',
        'location': 'The Castro',
        'available_start': '9:15',
        'available_end': '13:15',
        'duration': 30
    },
    {
        'name': 'Joseph',
        'location': 'Marina District',
        'available_start': '10:45',
        'available_end': '15:00',
        'duration': 90
    },
    {
        'name': 'Ashley',
        'location': 'Richmond District',
        'available_start': '9:45',
        'available_end': '11:15',
        'duration': 45
    },
    {
        'name': 'Patricia',
        'location': 'Union Square',
        'available_start': '16:30',
        'available_end': '20:00',
        'duration': 120
    },
    {
        'name': 'Karen',
        'location': 'Sunset District',
        'available_start': '16:30',
        'available_end': '22:00',
        'duration': 105
    }
]

def get_travel_time(from_loc, to_loc):
    return travel_times.get((from_loc, to_loc), float('inf'))

def is_schedule_valid(schedule):
    current_time = time_to_minutes('9:00')
    current_location = 'Financial District'
    
    for meeting in schedule:
        travel_time = get_travel_time(current_location, meeting['location'])
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(meeting['available_start'])
        available_end = time_to_minutes(meeting['available_end'])
        
        # Calculate meeting start time (latest of arrival and available start)
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + meeting['duration']
        
        if meeting_end > available_end:
            return False
        
        current_time = meeting_end
        current_location = meeting['location']
    
    return True

def calculate_total_meetings(schedule):
    return len(schedule)

def generate_possible_schedules(friends, max_permutations=1000):
    # Generate permutations of friends, but limit to max_permutations to avoid excessive computation
    from itertools import permutations, islice
    for perm in islice(permutations(friends), max_permutations):
        yield list(perm)

def find_best_schedule():
    best_schedule = []
    max_meetings = 0
    
    for schedule in generate_possible_schedules(friends, 1000):
        if is_schedule_valid(schedule):
            num_meetings = calculate_total_meetings(schedule)
            if num_meetings > max_meetings:
                max_meetings = num_meetings
                best_schedule = schedule
    
    return best_schedule

def build_itinerary(schedule):
    if not schedule:
        return {"itinerary": []}
    
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Financial District'
    
    for meeting in schedule:
        travel_time = get_travel_time(current_location, meeting['location'])
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(meeting['available_start'])
        available_end = time_to_minutes(meeting['available_end'])
        
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + meeting['duration']
        
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['name'],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = meeting['location']
    
    return {"itinerary": itinerary}

best_schedule = find_best_schedule()
result = build_itinerary(best_schedule)
print(json.dumps(result, indent=2))