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
    locations = ['Haight-Ashbury', 'Mission District', 'Bayview', 'Pacific Heights', 'Russian Hill', "Fisherman's Wharf"]
    
    # Travel times in minutes (from_location, to_location): time
    travel_times = {
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', "Fisherman's Wharf"): 23,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', "Fisherman's Wharf"): 22,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', "Fisherman's Wharf"): 25,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', "Fisherman's Wharf"): 13,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', "Fisherman's Wharf"): 7,
        ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
        ("Fisherman's Wharf", 'Mission District'): 22,
        ("Fisherman's Wharf", 'Bayview'): 26,
        ("Fisherman's Wharf", 'Pacific Heights'): 12,
        ("Fisherman's Wharf", 'Russian Hill'): 7
    }
    
    # Friend constraints
    friends = [
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
            'location': "Fisherman's Wharf",
            'available_start': '8:30',
            'available_end': '17:45',
            'min_duration': 60
        }
    ]
    
    # Initial conditions
    current_location = 'Haight-Ashbury'
    current_time = time_to_minutes('9:00')
    
    # Generate all possible orders to meet friends
    best_schedule = None
    max_friends_met = 0
    
    for order in permutations(friends):
        schedule = []
        temp_location = current_location
        temp_time = current_time
        friends_met = 0
        
        for friend in order:
            # Calculate travel time
            travel_time = travel_times.get((temp_location, friend['location']), float('inf'))
            arrival_time = temp_time + travel_time
            
            # Check if we can meet this friend
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            min_duration = friend['min_duration']
            
            # Calculate meeting window
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + min_duration
            
            if meeting_end <= available_end:
                # Can meet this friend
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                friends_met += 1
                temp_location = friend['location']
                temp_time = meeting_end
            else:
                # Can't meet this friend
                continue
        
        # Update best schedule if this one meets more friends
        if friends_met > max_friends_met:
            max_friends_met = friends_met
            best_schedule = schedule
        elif friends_met == max_friends_met and best_schedule is not None:
            # Prefer schedules that meet longer durations or end earlier
            pass
    
    return {'itinerary': best_schedule}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))