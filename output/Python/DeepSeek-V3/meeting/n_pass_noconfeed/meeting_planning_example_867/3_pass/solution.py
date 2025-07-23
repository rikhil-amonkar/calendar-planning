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
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10
}

# Friend constraints
friends = [
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'available_start': '10:30',
        'available_end': '20:00',
        'min_duration': 90
    },
    {
        'name': 'David',
        'location': 'Union Square',
        'available_start': '15:15',
        'available_end': '19:00',
        'min_duration': 45
    },
    {
        'name': 'Sandra',
        'location': 'Pacific Heights',
        'available_start': '7:00',
        'available_end': '20:00',
        'min_duration': 120
    },
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'available_start': '19:30',
        'available_end': '20:30',
        'min_duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Fisherman\'s Wharf',
        'available_start': '10:00',
        'available_end': '15:00',
        'min_duration': 15
    },
    {
        'name': 'Kenneth',
        'location': 'Marina District',
        'available_start': '10:45',
        'available_end': '13:00',
        'min_duration': 45
    },
    {
        'name': 'Melissa',
        'location': 'Richmond District',
        'available_start': '18:15',
        'available_end': '20:00',
        'min_duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'Sunset District',
        'available_start': '10:15',
        'available_end': '18:15',
        'min_duration': 105
    },
    {
        'name': 'Amanda',
        'location': 'Golden Gate Park',
        'available_start': '7:45',
        'available_end': '18:45',
        'min_duration': 15
    }
]

def get_travel_time(from_loc, to_loc):
    return travel_times.get((from_loc, to_loc), float('inf'))

def is_schedule_valid(schedule):
    current_time = time_to_minutes('9:00')
    current_location = 'Haight-Ashbury'
    
    for meeting in schedule:
        travel_time = get_travel_time(current_location, meeting['location'])
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(meeting['available_start'])
        available_end = time_to_minutes(meeting['available_end'])
        min_duration = meeting['min_duration']
        
        # Check if we can arrive before the available end time
        if arrival_time >= available_end:
            return False
        
        # Start time is max of arrival time and available start time
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        # Check if we can complete the meeting
        if end_time > available_end:
            return False
        
        current_time = end_time
        current_location = meeting['location']
    
    return True

def calculate_total_meetings(schedule):
    return len(schedule)

def generate_schedules():
    best_schedule = []
    max_meetings = 0
    
    # Try all permutations of friends up to 5 (since time is limited)
    for size in range(1, min(6, len(friends) + 1)):  # Fixed: added missing parenthesis
        for perm in permutations(friends, size):
            if is_schedule_valid(perm):
                if len(perm) > max_meetings:
                    max_meetings = len(perm)
                    best_schedule = perm
    
    return best_schedule

def convert_schedule_to_itinerary(schedule):
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Haight-Ashbury'
    
    for meeting in schedule:
        travel_time = get_travel_time(current_location, meeting['location'])
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(meeting['available_start'])
        available_end = time_to_minutes(meeting['available_end'])
        min_duration = meeting['min_duration']
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        itinerary.append({
            'action': 'meet',
            'location': meeting['location'],
            'person': meeting['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = meeting['location']
    
    return itinerary

best_schedule = generate_schedules()
itinerary = convert_schedule_to_itinerary(best_schedule)

output = {
    'itinerary': itinerary
}

print(json.dumps(output, indent=2))