import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        'The Castro': {
            'Bayview': 19,
            'Pacific Heights': 16,
            'Alamo Square': 8,
            'Fisherman\'s Wharf': 24,
            'Golden Gate Park': 11
        },
        'Bayview': {
            'The Castro': 20,
            'Pacific Heights': 23,
            'Alamo Square': 16,
            'Fisherman\'s Wharf': 25,
            'Golden Gate Park': 22
        },
        'Pacific Heights': {
            'The Castro': 16,
            'Bayview': 22,
            'Alamo Square': 10,
            'Fisherman\'s Wharf': 13,
            'Golden Gate Park': 15
        },
        'Alamo Square': {
            'The Castro': 8,
            'Bayview': 16,
            'Pacific Heights': 10,
            'Fisherman\'s Wharf': 19,
            'Golden Gate Park': 9
        },
        'Fisherman\'s Wharf': {
            'The Castro': 26,
            'Bayview': 26,
            'Pacific Heights': 12,
            'Alamo Square': 20,
            'Golden Gate Park': 25
        },
        'Golden Gate Park': {
            'The Castro': 13,
            'Bayview': 23,
            'Pacific Heights': 16,
            'Alamo Square': 10,
            'Fisherman\'s Wharf': 24
        }
    }
    
    friends = [
        {'name': 'Rebecca', 'location': 'Bayview', 'window': (540, 765)},
        {'name': 'Amanda', 'location': 'Pacific Heights', 'window': (1110, 1305)},
        {'name': 'James', 'location': 'Alamo Square', 'window': (585, 1275)},
        {'name': 'Sarah', 'location': 'Fisherman\'s Wharf', 'window': (480, 1290)},
        {'name': 'Melissa', 'location': 'Golden Gate Park', 'window': (540, 1125)}
    ]
    
    best_count = 0
    best_itinerary = []
    
    for perm in itertools.permutations(friends):
        current_location = 'The Castro'
        current_time = 540
        itinerary_this = []
        
        for friend in perm:
            next_loc = friend['location']
            travel_duration = travel_times[current_location][next_loc]
            current_time += travel_duration
            current_location = next_loc
            
            window_start, window_end = friend['window']
            meeting_start = max(current_time, window_start)
            if meeting_start + 90 <= window_end:
                meeting_end = meeting_start + 90
                itinerary_this.append({
                    'action': 'meet',
                    'location': next_loc,
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                current_time = meeting_end
        
        if len(itinerary_this) > best_count:
            best_count = len(itinerary_this)
            best_itinerary = itinerary_this
            if best_count == 5:
                break
    
    result = {"itinerary": best_itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()