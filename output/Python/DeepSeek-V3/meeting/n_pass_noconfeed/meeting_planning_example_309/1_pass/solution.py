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
    # Locations
    locations = ['Financial District', 'Chinatown', 'Alamo Square', 'Bayview', 'Fisherman\'s Wharf']
    
    # Travel times (in minutes) as a dictionary: (from, to) -> time
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
        ('Fisherman\'s Wharf', 'Bayview'): 26
    }
    
    # Constraints
    constraints = {
        'Nancy': {
            'location': 'Chinatown',
            'start': time_to_minutes('9:30'),
            'end': time_to_minutes('13:30'),
            'duration': 90
        },
        'Mary': {
            'location': 'Alamo Square',
            'start': time_to_minutes('7:00'),
            'end': time_to_minutes('21:00'),
            'duration': 75
        },
        'Jessica': {
            'location': 'Bayview',
            'start': time_to_minutes('11:15'),
            'end': time_to_minutes('13:45'),
            'duration': 45
        },
        'Rebecca': {
            'location': 'Fisherman\'s Wharf',
            'start': time_to_minutes('7:00'),
            'end': time_to_minutes('8:30'),
            'duration': 45
        }
    }
    
    # Initial position and time
    current_location = 'Financial District'
    current_time = time_to_minutes('9:00')
    
    # Since Rebecca is only available before 8:30AM, she cannot be met
    # So we consider only Nancy, Mary, and Jessica
    people = ['Nancy', 'Mary', 'Jessica']
    
    best_schedule = []
    max_meetings = 0
    
    # Try all permutations of meeting order
    for order in permutations(people):
        schedule = []
        temp_location = current_location
        temp_time = current_time
        meetings = 0
        
        for person in order:
            info = constraints[person]
            loc = info['location']
            start = info['start']
            end = info['end']
            duration = info['duration']
            
            # Travel time
            travel_time = travel_times.get((temp_location, loc), float('inf'))
            arrival_time = temp_time + travel_time
            
            # Check if we can meet
            if arrival_time > end:
                continue  # Cannot meet this person
            
            # Calculate meeting start and end
            meeting_start = max(arrival_time, start)
            meeting_end = meeting_start + duration
            
            if meeting_end > end:
                continue  # Not enough time
            
            # Add to schedule
            schedule.append({
                'action': 'meet',
                'location': loc,
                'person': person,
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            
            meetings += 1
            temp_location = loc
            temp_time = meeting_end
        
        if meetings > max_meetings:
            max_meetings = meetings
            best_schedule = schedule
        elif meetings == max_meetings and meetings > 0:
            # Prefer schedules that end earlier
            if temp_time < time_to_minutes(best_schedule[-1]['end_time']):
                best_schedule = schedule
    
    return {'itinerary': best_schedule}

if __name__ == '__main__':
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))