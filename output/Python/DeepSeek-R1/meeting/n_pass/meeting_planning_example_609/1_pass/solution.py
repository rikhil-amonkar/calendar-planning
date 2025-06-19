import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times matrix
    locations = [
        'Chinatown', 'Mission District', 'Alamo Square', 'Pacific Heights',
        'Union Square', 'Golden Gate Park', 'Sunset District', 'Presidio'
    ]
    travel_times = {loc: {} for loc in locations}
    
    travel_data = [
        ('Chinatown', 'Mission District', 18),
        ('Chinatown', 'Alamo Square', 17),
        ('Chinatown', 'Pacific Heights', 10),
        ('Chinatown', 'Union Square', 7),
        ('Chinatown', 'Golden Gate Park', 23),
        ('Chinatown', 'Sunset District', 29),
        ('Chinatown', 'Presidio', 19),
        ('Mission District', 'Chinatown', 16),
        ('Mission District', 'Alamo Square', 11),
        ('Mission District', 'Pacific Heights', 16),
        ('Mission District', 'Union Square', 15),
        ('Mission District', 'Golden Gate Park', 17),
        ('Mission District', 'Sunset District', 24),
        ('Mission District', 'Presidio', 25),
        ('Alamo Square', 'Chinatown', 16),
        ('Alamo Square', 'Mission District', 10),
        ('Alamo Square', 'Pacific Heights', 10),
        ('Alamo Square', 'Union Square', 14),
        ('Alamo Square', 'Golden Gate Park', 9),
        ('Alamo Square', 'Sunset District', 16),
        ('Alamo Square', 'Presidio', 18),
        ('Pacific Heights', 'Chinatown', 11),
        ('Pacific Heights', 'Mission District', 15),
        ('Pacific Heights', 'Alamo Square', 10),
        ('Pacific Heights', 'Union Square', 12),
        ('Pacific Heights', 'Golden Gate Park', 15),
        ('Pacific Heights', 'Sunset District', 21),
        ('Pacific Heights', 'Presidio', 11),
        ('Union Square', 'Chinatown', 7),
        ('Union Square', 'Mission District', 14),
        ('Union Square', 'Alamo Square', 15),
        ('Union Square', 'Pacific Heights', 15),
        ('Union Square', 'Golden Gate Park', 22),
        ('Union Square', 'Sunset District', 26),
        ('Union Square', 'Presidio', 24),
        ('Golden Gate Park', 'Chinatown', 23),
        ('Golden Gate Park', 'Mission District', 17),
        ('Golden Gate Park', 'Alamo Square', 10),
        ('Golden Gate Park', 'Pacific Heights', 16),
        ('Golden Gate Park', 'Union Square', 22),
        ('Golden Gate Park', 'Sunset District', 10),
        ('Golden Gate Park', 'Presidio', 11),
        ('Sunset District', 'Chinatown', 30),
        ('Sunset District', 'Mission District', 24),
        ('Sunset District', 'Alamo Square', 17),
        ('Sunset District', 'Pacific Heights', 21),
        ('Sunset District', 'Union Square', 30),
        ('Sunset District', 'Golden Gate Park', 11),
        ('Sunset District', 'Presidio', 16),
        ('Presidio', 'Chinatown', 21),
        ('Presidio', 'Mission District', 26),
        ('Presidio', 'Alamo Square', 18),
        ('Presidio', 'Pacific Heights', 11),
        ('Presidio', 'Union Square', 22),
        ('Presidio', 'Golden Gate Park', 12),
        ('Presidio', 'Sunset District', 15)
    ]
    
    for from_loc, to_loc, time_val in travel_data:
        travel_times[from_loc][to_loc] = time_val

    # Define friends' constraints (excluding Carol)
    friends = [
        {'name': 'David', 'location': 'Mission District', 
         'start_available': 8 * 60, 'end_available': 19 * 60 + 45, 'min_duration': 45},
        {'name': 'Kenneth', 'location': 'Alamo Square', 
         'start_available': 14 * 60, 'end_available': 19 * 60 + 45, 'min_duration': 120},
        {'name': 'John', 'location': 'Pacific Heights', 
         'start_available': 17 * 60, 'end_available': 20 * 60, 'min_duration': 15},
        {'name': 'Charles', 'location': 'Union Square', 
         'start_available': 21 * 60 + 45, 'end_available': 22 * 60 + 45, 'min_duration': 60},
        {'name': 'Deborah', 'location': 'Golden Gate Park', 
         'start_available': 7 * 60, 'end_available': 18 * 60 + 15, 'min_duration': 90},
        {'name': 'Karen', 'location': 'Sunset District', 
         'start_available': 17 * 60 + 45, 'end_available': 21 * 60 + 15, 'min_duration': 15}
    ]
    
    start_location = 'Chinatown'
    start_time = 9 * 60  # 9:00 AM in minutes
    best_itinerary = None
    found = False
    n = len(friends)
    
    # Try to find a feasible schedule with maximum meetings
    for r in range(n, 0, -1):
        for subset in itertools.combinations(friends, r):
            for perm in itertools.permutations(subset):
                current_loc = start_location
                current_time_val = start_time
                itinerary = []
                valid = True
                
                for friend in perm:
                    to_loc = friend['location']
                    travel_duration = travel_times[current_loc][to_loc]
                    current_time_val += travel_duration
                    
                    # Calculate meeting start and end times
                    meeting_start = max(current_time_val, friend['start_available'])
                    meeting_end = meeting_start + friend['min_duration']
                    
                    # Check if meeting fits within friend's availability
                    if meeting_end > friend['end_available']:
                        valid = False
                        break
                    
                    # Record meeting
                    itinerary.append({
                        'action': 'meet',
                        'location': to_loc,
                        'person': friend['name'],
                        'start_time': minutes_to_time(meeting_start),
                        'end_time': minutes_to_time(meeting_end)
                    })
                    
                    current_time_val = meeting_end
                    current_loc = to_loc
                
                if valid:
                    best_itinerary = itinerary
                    found = True
                    break
            if found:
                break
        if found:
            break
    
    # Prepare output
    if best_itinerary is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": best_itinerary}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()