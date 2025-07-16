import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Travel times in minutes (from_location, to_location): time
    travel_times = {
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Bayview'): 22,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
    }

    # Constraints
    constraints = [
        {
            'name': 'Nancy',
            'location': 'Chinatown',
            'available_start': '9:30',
            'available_end': '13:30',
            'duration': 90
        },
        {
            'name': 'Mary',
            'location': 'Alamo Square',
            'available_start': '7:00',
            'available_end': '21:00',
            'duration': 75
        },
        {
            'name': 'Jessica',
            'location': 'Bayview',
            'available_start': '11:15',
            'available_end': '13:45',
            'duration': 45
        },
        {
            'name': 'Rebecca',
            'location': 'Fisherman\'s Wharf',
            'available_start': '7:00',
            'available_end': '8:30',
            'duration': 45
        }
    ]

    # Start early to meet Rebecca
    current_time = time_to_minutes('6:30')  # Starting earlier to accommodate Rebecca
    current_location = 'Financial District'
    itinerary = []

    # First meet Rebecca (must be done early)
    rebecca = next(p for p in constraints if p['name'] == 'Rebecca')
    travel_time = travel_times[(current_location, rebecca['location'])]
    arrival_time = current_time + travel_time
    available_start = time_to_minutes(rebecca['available_start'])
    available_end = time_to_minutes(rebecca['available_end'])
    
    if arrival_time <= available_end - rebecca['duration']:
        start_time = max(arrival_time, available_start)
        end_time = start_time + rebecca['duration']
        itinerary.append({
            'action': 'meet',
            'location': rebecca['location'],
            'person': rebecca['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = rebecca['location']
    else:
        # If we can't meet Rebecca, just return empty
        return []

    # Now try to meet others in best possible order
    remaining_people = [p for p in constraints if p['name'] != 'Rebecca']
    best_itinerary = []
    max_meetings = 0

    # Try all permutations of remaining people to find best schedule
    for order in permutations(remaining_people):
        temp_itinerary = itinerary.copy()
        temp_current_time = current_time
        temp_current_location = current_location
        meetings = 1  # Already met Rebecca
        
        for person in order:
            travel_time = travel_times.get((temp_current_location, person['location']), float('inf'))
            arrival_time = temp_current_time + travel_time
            available_start = time_to_minutes(person['available_start'])
            available_end = time_to_minutes(person['available_end'])
            
            if arrival_time <= available_end - person['duration']:
                start_time = max(arrival_time, available_start)
                end_time = start_time + person['duration']
                temp_itinerary.append({
                    'action': 'meet',
                    'location': person['location'],
                    'person': person['name'],
                    'start_time': minutes_to_time(start_time),
                    'end_time': minutes_to_time(end_time)
                })
                temp_current_time = end_time
                temp_current_location = person['location']
                meetings += 1

        # Check if this schedule is better
        if meetings > max_meetings or (meetings == max_meetings and temp_current_time < time_to_minutes('21:00')):
            max_meetings = meetings
            best_itinerary = temp_itinerary

    return best_itinerary

result = {
    "itinerary": calculate_schedule()
}
print(json.dumps(result, indent=2))