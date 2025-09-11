import itertools
import json

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
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
    
    friends = {
        'Nancy': {
            'location': 'Chinatown',
            'start_avail': time_to_minutes('9:30'),
            'end_avail': time_to_minutes('13:30'),
            'min_dur': 90
        },
        'Mary': {
            'location': 'Alamo Square',
            'start_avail': time_to_minutes('7:00'),
            'end_avail': time_to_minutes('21:00'),
            'min_dur': 75
        },
        'Jessica': {
            'location': 'Bayview',
            'start_avail': time_to_minutes('11:15'),
            'end_avail': time_to_minutes('13:45'),
            'min_dur': 45
        }
    }
    
    start_time = time_to_minutes('9:00')
    start_location = 'Financial District'
    best_itinerary = []
    max_met = 0
    
    for k in range(3, 0, -1):
        for friend_subset in itertools.combinations(friends.keys(), k):
            for order in itertools.permutations(friend_subset):
                current_time = start_time
                current_loc = start_location
                itinerary = []
                valid = True
                
                for friend in order:
                    data = friends[friend]
                    travel_key = (current_loc, data['location'])
                    if travel_key not in travel_times:
                        valid = False
                        break
                    travel_duration = travel_times[travel_key]
                    current_time += travel_duration
                    start_meeting = max(current_time, data['start_avail'])
                    end_meeting = start_meeting + data['min_dur']
                    
                    if end_meeting > data['end_avail']:
                        valid = False
                        break
                    
                    itinerary.append({
                        'action': 'meet',
                        'location': data['location'],
                        'person': friend,
                        'start_time': minutes_to_time(start_meeting),
                        'end_time': minutes_to_time(end_meeting)
                    })
                    
                    current_time = end_meeting
                    current_loc = data['location']
                
                if valid and len(itinerary) > max_met:
                    best_itinerary = itinerary
                    max_met = len(itinerary)
                    break
            if max_met == k:
                break
        if max_met > 0:
            break
    
    result = {'itinerary': best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()