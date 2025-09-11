import itertools
import json

def time_to_minutes(time_str):
    if 'AM' in time_str or 'PM' in time_str:
        time_str = time_str.replace('AM', '').replace('PM', '').strip()
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hours * 60 + minutes

def minutes_to_time(minutes_since_midnight):
    total_minutes = minutes_since_midnight
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    travel_times = {
        'Pacific Heights': {'Nob Hill': 8, 'Russian Hill': 7, 'The Castro': 16, 'Sunset District': 21, 'Haight-Ashbury': 11},
        'Nob Hill': {'Pacific Heights': 8, 'Russian Hill': 5, 'The Castro': 17, 'Sunset District': 25, 'Haight-Ashbury': 13},
        'Russian Hill': {'Pacific Heights': 7, 'Nob Hill': 5, 'The Castro': 21, 'Sunset District': 23, 'Haight-Ashbury': 17},
        'The Castro': {'Pacific Heights': 16, 'Nob Hill': 16, 'Russian Hill': 18, 'Sunset District': 17, 'Haight-Ashbury': 6},
        'Sunset District': {'Pacific Heights': 21, 'Nob Hill': 27, 'Russian Hill': 24, 'The Castro': 17, 'Haight-Ashbury': 15},
        'Haight-Ashbury': {'Pacific Heights': 12, 'Nob Hill': 15, 'Russian Hill': 17, 'The Castro': 6, 'Sunset District': 15}
    }
    
    base_time = time_to_minutes('9:00AM')
    
    friends = [
        {'name': 'Ronald', 'location': 'Nob Hill', 'window_start': time_to_minutes('10:00AM') - base_time, 'window_end': time_to_minutes('5:00PM') - base_time, 'min_duration': 105},
        {'name': 'Helen', 'location': 'The Castro', 'window_start': time_to_minutes('1:30PM') - base_time, 'window_end': time_to_minutes('5:00PM') - base_time, 'min_duration': 120},
        {'name': 'Joshua', 'location': 'Sunset District', 'window_start': time_to_minutes('2:15PM') - base_time, 'window_end': time_to_minutes('7:30PM') - base_time, 'min_duration': 90},
        {'name': 'Margaret', 'location': 'Haight-Ashbury', 'window_start': time_to_minutes('10:15AM') - base_time, 'window_end': time_to_minutes('10:00PM') - base_time, 'min_duration': 60}
    ]
    
    best_itinerary = []
    max_friends = 0
    
    for n in range(len(friends), 0, -1):
        for subset in itertools.combinations(friends, n):
            for perm in itertools.permutations(subset):
                current_location = 'Pacific Heights'
                current_time = 0
                itinerary = []
                valid = True
                
                for friend in perm:
                    travel_time = travel_times[current_location][friend['location']]
                    arrival_time = current_time + travel_time
                    
                    if arrival_time > friend['window_end']:
                        valid = False
                        break
                    
                    start_time = max(arrival_time, friend['window_start'])
                    end_time = start_time + friend['min_duration']
                    
                    if end_time > friend['window_end']:
                        valid = False
                        break
                    
                    itinerary.append({
                        'friend': friend,
                        'start_time': start_time,
                        'end_time': end_time
                    })
                    
                    current_time = end_time
                    current_location = friend['location']
                
                if valid and len(itinerary) > max_friends:
                    max_friends = len(itinerary)
                    best_itinerary = itinerary
                    break
            
            if best_itinerary:
                break
        
        if best_itinerary:
            break
    
    result = []
    for meeting in best_itinerary:
        friend = meeting['friend']
        start_absolute = base_time + meeting['start_time']
        end_absolute = base_time + meeting['end_time']
        result.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_absolute),
            'end_time': minutes_to_time(end_absolute)
        })
    
    output = {'itinerary': result}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()