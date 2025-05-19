import itertools
import json

def main():
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    friends = [
        {
            'name': 'Betty',
            'location': 'Embarcadero',
            'start': 19 * 60 + 45,
            'end': 21 * 60 + 45,
            'duration': 15
        },
        {
            'name': 'Karen',
            'location': 'Fisherman\'s Wharf',
            'start': 8 * 60 + 45,
            'end': 15 * 60,
            'duration': 30
        },
        {
            'name': 'Anthony',
            'location': 'Financial District',
            'start': 9 * 60 + 15,
            'end': 21 * 60 + 30,
            'duration': 105
        }
    ]
    
    travel_times = {
        'Bayview': {
            'Embarcadero': 19,
            'Fisherman\'s Wharf': 25,
            'Financial District': 19
        },
        'Embarcadero': {
            'Bayview': 21,
            'Fisherman\'s Wharf': 6,
            'Financial District': 5
        },
        'Fisherman\'s Wharf': {
            'Bayview': 26,
            'Embarcadero': 8,
            'Financial District': 11
        },
        'Financial District': {
            'Bayview': 19,
            'Embarcadero': 4,
            'Fisherman\'s Wharf': 10
        }
    }
    
    for perm in itertools.permutations(friends):
        current_time = 9 * 60
        current_location = 'Bayview'
        itinerary = []
        possible = True
        
        for friend in perm:
            to_loc = friend['location']
            travel = travel_times[current_location].get(to_loc)
            if travel is None:
                possible = False
                break
            arrival = current_time + travel
            start = max(arrival, friend['start'])
            latest_start = friend['end'] - friend['duration']
            if start > latest_start:
                possible = False
                break
            end = start + friend['duration']
            itinerary.append({
                'action': 'meet',
                'location': to_loc,
                'person': friend['name'],
                'start_time': format_time(start),
                'end_time': format_time(end)
            })
            current_time = end
            current_location = to_loc
        
        if possible:
            print(json.dumps({'itinerary': itinerary}, indent=2))
            return
    
    print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()