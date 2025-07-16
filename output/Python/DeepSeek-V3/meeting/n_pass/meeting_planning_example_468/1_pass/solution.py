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
locations = ['The Castro', 'Bayview', 'Pacific Heights', 'Alamo Square', 'Fisherman\'s Wharf', 'Golden Gate Park']
travel_times = {
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Bayview', 'The Castro'): 20,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24
}

people = {
    'Rebecca': {'location': 'Bayview', 'start': '9:00', 'end': '12:45', 'min_duration': 90},
    'Amanda': {'location': 'Pacific Heights', 'start': '18:30', 'end': '21:45', 'min_duration': 90},
    'James': {'location': 'Alamo Square', 'start': '9:45', 'end': '21:15', 'min_duration': 90},
    'Sarah': {'location': 'Fisherman\'s Wharf', 'start': '8:00', 'end': '21:30', 'min_duration': 90},
    'Melissa': {'location': 'Golden Gate Park', 'start': '9:00', 'end': '18:45', 'min_duration': 90}
}

current_time = time_to_minutes('9:00')
current_location = 'The Castro'

# Generate all possible orders to meet people
people_names = list(people.keys())
best_schedule = None
max_meetings = 0

for order in permutations(people_names):
    schedule = []
    temp_time = current_time
    temp_location = current_location
    meetings = 0
    feasible = True
    
    for person in order:
        info = people[person]
        loc = info['location']
        travel_time = travel_times.get((temp_location, loc), float('inf'))
        arrival_time = temp_time + travel_time
        start_window = time_to_minutes(info['start'])
        end_window = time_to_minutes(info['end'])
        min_duration = info['min_duration']
        
        # Calculate meeting start and end
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > end_window:
            feasible = False
            break
        
        schedule.append({
            'action': 'meet',
            'location': loc,
            'person': person,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        temp_time = meeting_end
        temp_location = loc
        meetings += 1
    
    if feasible and meetings > max_meetings:
        max_meetings = meetings
        best_schedule = schedule

# If no schedule meets all, try subsets
if best_schedule is None:
    from itertools import combinations
    for r in range(len(people_names), 0, -1):
        for subset in combinations(people_names, r):
            for order in permutations(subset):
                schedule = []
                temp_time = current_time
                temp_location = current_location
                meetings = 0
                feasible = True
                
                for person in order:
                    info = people[person]
                    loc = info['location']
                    travel_time = travel_times.get((temp_location, loc), float('inf'))
                    arrival_time = temp_time + travel_time
                    start_window = time_to_minutes(info['start'])
                    end_window = time_to_minutes(info['end'])
                    min_duration = info['min_duration']
                    
                    meeting_start = max(arrival_time, start_window)
                    meeting_end = meeting_start + min_duration
                    
                    if meeting_end > end_window:
                        feasible = False
                        break
                    
                    schedule.append({
                        'action': 'meet',
                        'location': loc,
                        'person': person,
                        'start_time': minutes_to_time(meeting_start),
                        'end_time': minutes_to_time(meeting_end)
                    })
                    
                    temp_time = meeting_end
                    temp_location = loc
                    meetings += 1
                
                if feasible and meetings > max_meetings:
                    max_meetings = meetings
                    best_schedule = schedule
                    if max_meetings == len(people_names):
                        break
                if max_meetings == len(people_names):
                    break
            if max_meetings == len(people_names):
                break
        if max_meetings == len(people_names):
            break

# Output the best schedule found
if best_schedule:
    output = {"itinerary": best_schedule}
else:
    output = {"itinerary": []}

print(json.dumps(output, indent=2))