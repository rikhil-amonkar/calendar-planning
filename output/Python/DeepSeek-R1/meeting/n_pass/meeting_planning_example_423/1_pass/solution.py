import itertools
import json
from collections import namedtuple

def main():
    travel_matrix = {
        'Presidio': {
            'Richmond District': 7,
            'North Beach': 18,
            'Financial District': 23,
            'Golden Gate Park': 12,
            'Union Square': 22
        },
        'Richmond District': {
            'Presidio': 7,
            'North Beach': 17,
            'Financial District': 22,
            'Golden Gate Park': 9,
            'Union Square': 21
        },
        'North Beach': {
            'Presidio': 17,
            'Richmond District': 18,
            'Financial District': 8,
            'Golden Gate Park': 22,
            'Union Square': 7
        },
        'Financial District': {
            'Presidio': 22,
            'Richmond District': 21,
            'North Beach': 7,
            'Golden Gate Park': 23,
            'Union Square': 9
        },
        'Golden Gate Park': {
            'Presidio': 11,
            'Richmond District': 7,
            'North Beach': 24,
            'Financial District': 26,
            'Union Square': 22
        },
        'Union Square': {
            'Presidio': 24,
            'Richmond District': 20,
            'North Beach': 10,
            'Financial District': 9,
            'Golden Gate Park': 22
        }
    }
    
    Friend = namedtuple('Friend', ['name', 'location', 'start', 'end', 'duration'])
    friends = [
        Friend('Jason', 'Richmond District', 13*60, 20*60+45, 90),
        Friend('Melissa', 'North Beach', 18*60+45, 20*60+15, 45),
        Friend('Brian', 'Financial District', 9*60+45, 21*60+45, 15),
        Friend('Elizabeth', 'Golden Gate Park', 8*60+45, 21*60+30, 105),
        Friend('Laura', 'Union Square', 14*60+15, 19*60+30, 75)
    ]
    
    start_time = 9 * 60
    start_location = 'Presidio'
    max_count = 0
    best_itinerary = None
    
    for perm in itertools.permutations(friends):
        current_location = start_location
        current_time = start_time
        itinerary_this = []
        count = 0
        
        for friend in perm:
            travel_time = travel_matrix[current_location][friend.location]
            arrival_time = current_time + travel_time
            meeting_start = max(arrival_time, friend.start)
            
            if meeting_start > friend.end - friend.duration:
                continue
                
            meeting_end = meeting_start + friend.duration
            if meeting_end > friend.end:
                continue
                
            itinerary_this.append((friend, meeting_start, meeting_end))
            current_time = meeting_end
            current_location = friend.location
            count += 1
            
        if count > max_count:
            max_count = count
            best_itinerary = itinerary_this
            if count == len(friends):
                break
                
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    itinerary_json = []
    if best_itinerary is not None:
        for meeting in best_itinerary:
            friend, start, end = meeting
            itinerary_json.append({
                "action": "meet",
                "location": friend.location,
                "person": friend.name,
                "start_time": format_time(start),
                "end_time": format_time(end)
            })
    
    result = {"itinerary": itinerary_json}
    print(json.dumps(result))

if __name__ == "__main__":
    main()