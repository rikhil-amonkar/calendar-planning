import json
from itertools import permutations

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        'The Castro': {
            'Mission District': 7,
            'Financial District': 20
        },
        'Mission District': {
            'The Castro': 7,
            'Financial District': 17
        },
        'Financial District': {
            'The Castro': 23,
            'Mission District': 17
        }
    }
    
    people = {
        'Laura': {
            'location': 'Mission District',
            'available_start': '12:15',
            'available_end': '19:45',
            'min_duration': 75
        },
        'Anthony': {
            'location': 'Financial District',
            'available_start': '12:30',
            'available_end': '14:45',
            'min_duration': 30
        }
    }
    
    start_location = 'The Castro'
    start_time = '9:00'
    current_time = time_to_minutes(start_time)
    
    best_itinerary = None
    best_finish = float('inf')
    
    for order in permutations(people.keys()):
        itinerary = []
        current_loc = start_location
        current_time_temp = current_time
        
        feasible = True
        for person in order:
            info = people[person]
            target_loc = info['location']
            travel_time = travel_times[current_loc][target_loc]
            arrival_time = current_time_temp + travel_time
            avail_start = time_to_minutes(info['available_start'])
            avail_end = time_to_minutes(info['available_end'])
            
            meeting_start = max(arrival_time, avail_start)
            meeting_end = meeting_start + info['min_duration']
            
            if meeting_end > avail_end:
                feasible = False
                break
                
            itinerary.append({
                'action': 'meet',
                'location': target_loc,
                'person': person,
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            
            current_time_temp = meeting_end
            current_loc = target_loc
            
        if feasible and current_time_temp < best_finish:
            best_finish = current_time_temp
            best_itinerary = itinerary
            
    if best_itinerary is None:
        best_itinerary = []
        
    output = {'itinerary': best_itinerary}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()