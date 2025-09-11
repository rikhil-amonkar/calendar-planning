import itertools
import json

def main():
    # Travel times dictionary
    travel_times = {
        'Golden Gate Park': {
            'Haight-Ashbury': 7,
            'Fisherman\'s Wharf': 24,
            'The Castro': 13,
            'Chinatown': 23,
            'Alamo Square': 10,
            'North Beach': 24,
            'Russian Hill': 19
        },
        'Haight-Ashbury': {
            'Golden Gate Park': 7,
            'Fisherman\'s Wharf': 23,
            'The Castro': 6,
            'Chinatown': 19,
            'Alamo Square': 5,
            'North Beach': 19,
            'Russian Hill': 17
        },
        'Fisherman\'s Wharf': {
            'Golden Gate Park': 25,
            'Haight-Ashbury': 22,
            'The Castro': 26,
            'Chinatown': 12,
            'Alamo Square': 20,
            'North Beach': 6,
            'Russian Hill': 7
        },
        'The Castro': {
            'Golden Gate Park': 11,
            'Haight-Ashbury': 6,
            'Fisherman\'s Wharf': 24,
            'Chinatown': 20,
            'Alamo Square': 8,
            'North Beach': 20,
            'Russian Hill': 18
        },
        'Chinatown': {
            'Golden Gate Park': 23,
            'Haight-Ashbury': 19,
            'Fisherman\'s Wharf': 8,
            'The Castro': 22,
            'Alamo Square': 17,
            'North Beach': 3,
            'Russian Hill': 7
        },
        'Alamo Square': {
            'Golden Gate Park': 9,
            'Haight-Ashbury': 5,
            'Fisherman\'s Wharf': 19,
            'The Castro': 8,
            'Chinatown': 16,
            'North Beach': 15,
            'Russian Hill': 13
        },
        'North Beach': {
            'Golden Gate Park': 22,
            'Haight-Ashbury': 18,
            'Fisherman\'s Wharf': 5,
            'The Castro': 22,
            'Chinatown': 6,
            'Alamo Square': 16,
            'Russian Hill': 4
        },
        'Russian Hill': {
            'Golden Gate Park': 21,
            'Haight-Ashbury': 17,
            'Fisherman\'s Wharf': 7,
            'The Castro': 21,
            'Chinatown': 9,
            'Alamo Square': 15,
            'North Beach': 5
        }
    }
    
    # Friends data with adjusted times in minutes from 9:00 AM
    friends = [
        {'name': 'Carol', 'location': 'Haight-Ashbury', 'window_start': 750, 'window_end': 810, 'min_duration': 60},
        {'name': 'Laura', 'location': 'Fisherman\'s Wharf', 'window_start': 165, 'window_end': 750, 'min_duration': 60},
        {'name': 'Karen', 'location': 'The Castro', 'window_start': 0, 'window_end': 300, 'min_duration': 75},
        {'name': 'Elizabeth', 'location': 'Chinatown', 'window_start': 195, 'window_end': 750, 'min_duration': 75},
        {'name': 'Deborah', 'location': 'Alamo Square', 'window_start': 180, 'window_end': 360, 'min_duration': 105},
        {'name': 'Jason', 'location': 'North Beach', 'window_start': 345, 'window_end': 600, 'min_duration': 90},
        {'name': 'Steven', 'location': 'Russian Hill', 'window_start': 345, 'window_end': 570, 'min_duration': 120}
    ]
    
    # Helper function to convert minutes from midnight to time string
    def minutes_to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Try to find the largest feasible subset
    best_itinerary = []
    found = False
    n = len(friends)
    
    for k in range(n, 0, -1):
        for subset in itertools.combinations(friends, k):
            for perm in itertools.permutations(subset):
                current_time = 0
                current_loc = 'Golden Gate Park'
                itinerary = []
                valid = True
                
                for friend in perm:
                    travel = travel_times[current_loc][friend['location']]
                    current_time += travel
                    start_time = max(current_time, friend['window_start'])
                    end_time = start_time + friend['min_duration']
                    
                    if end_time > friend['window_end']:
                        valid = False
                        break
                    
                    itinerary.append({
                        'action': 'meet',
                        'location': friend['location'],
                        'person': friend['name'],
                        'start_time': start_time,
                        'end_time': end_time
                    })
                    
                    current_time = end_time
                    current_loc = friend['location']
                
                if valid:
                    best_itinerary = itinerary
                    found = True
                    break
            if found:
                break
        if found:
            break
    
    # Convert times to 24-hour format
    for event in best_itinerary:
        event['start_time'] = minutes_to_time_str(540 + event['start_time'])
        event['end_time'] = minutes_to_time_str(540 + event['end_time'])
    
    # Output as JSON
    result = {'itinerary': best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()