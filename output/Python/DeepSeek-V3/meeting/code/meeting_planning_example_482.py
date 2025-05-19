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
    locations = ['Haight-Ashbury', 'Mission District', 'Bayview', 'Pacific Heights', 'Russian Hill', 'Fisherman\'s Wharf']
    
    # Travel times (from_location, to_location): minutes
    travel_times = {
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7
    }
    
    # People and their constraints
    people = [
        {
            'name': 'Stephanie',
            'location': 'Mission District',
            'available_start': '8:15',
            'available_end': '13:45',
            'min_duration': 90
        },
        {
            'name': 'Sandra',
            'location': 'Bayview',
            'available_start': '13:00',
            'available_end': '19:30',
            'min_duration': 15
        },
        {
            'name': 'Richard',
            'location': 'Pacific Heights',
            'available_start': '7:15',
            'available_end': '10:15',
            'min_duration': 75
        },
        {
            'name': 'Brian',
            'location': 'Russian Hill',
            'available_start': '12:15',
            'available_end': '16:00',
            'min_duration': 120
        },
        {
            'name': 'Jason',
            'location': 'Fisherman\'s Wharf',
            'available_start': '8:30',
            'available_end': '17:45',
            'min_duration': 60
        }
    ]
    
    # Current time starts at 9:00 AM at Haight-Ashbury
    current_time = time_to_minutes('9:00')
    current_location = 'Haight-Ashbury'
    
    # Generate all possible orders to meet people
    best_schedule = []
    max_meetings = 0
    
    for order in permutations(people):
        schedule = []
        temp_time = current_time
        temp_location = current_location
        meetings = 0
        
        for person in order:
            # Calculate travel time
            travel_time = travel_times.get((temp_location, person['location']), None)
            if travel_time is None:
                continue  # Shouldn't happen as all pairs are defined
            
            arrival_time = temp_time + travel_time
            available_start = time_to_minutes(person['available_start'])
            available_end = time_to_minutes(person['available_end'])
            
            # Check if we can meet this person
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + person['min_duration']
            
            if meeting_end <= available_end:
                schedule.append({
                    'action': 'meet',
                    'location': person['location'],
                    'person': person['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                meetings += 1
                temp_time = meeting_end
                temp_location = person['location']
            else:
                break  # Can't meet this person in this order
        
        if meetings > max_meetings:
            max_meetings = meetings
            best_schedule = schedule
        elif meetings == max_meetings and len(schedule) > len(best_schedule):
            best_schedule = schedule
    
    return {'itinerary': best_schedule}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))