import json
from itertools import permutations

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}" if mins != 0 else f"{hours}:00"

def main():
    friends = [
        {
            'name': 'Melissa',
            'location': 'Golden Gate Park',
            'start': 8 * 60 + 30,
            'end': 20 * 60,
            'duration': 15
        },
        {
            'name': 'Nancy',
            'location': 'Presidio',
            'start': 19 * 60 + 45,
            'end': 22 * 60,
            'duration': 105
        },
        {
            'name': 'Emily',
            'location': 'Richmond District',
            'start': 16 * 60 + 45,
            'end': 22 * 60,
            'duration': 120
        }
    ]

    travel_times = {
        'Fisherman\'s Wharf': {
            'Golden Gate Park': 25,
            'Presidio': 17,
            'Richmond District': 18
        },
        'Golden Gate Park': {
            'Fisherman\'s Wharf': 24,
            'Presidio': 11,
            'Richmond District': 7
        },
        'Presidio': {
            'Fisherman\'s Wharf': 19,
            'Golden Gate Park': 12,
            'Richmond District': 7
        },
        'Richmond District': {
            'Fisherman\'s Wharf': 18,
            'Golden Gate Park': 9,
            'Presidio': 7
        }
    }

    best_itinerary = []
    max_met = 0

    for perm in permutations(friends):
        current_loc = 'Fisherman\'s Wharf'
        current_time = 9 * 60
        itinerary = []
        valid = True

        for friend in perm:
            dest = friend['location']
            tt = travel_times[current_loc].get(dest)
            if tt is None:
                valid = False
                break
            arrival = current_time + tt
            start = max(arrival, friend['start'])
            end = start + friend['duration']
            if end > friend['end']:
                valid = False
                break
            itinerary.append({
                'location': friend['location'],
                'person': friend['name'],
                'start': start,
                'end': end
            })
            current_time = end
            current_loc = dest

        if valid and len(itinerary) > max_met:
            max_met = len(itinerary)
            best_itinerary = itinerary
        elif valid and len(itinerary) == max_met and best_itinerary:
            current_last = max([item['end'] for item in itinerary])
            best_last = max([item['end'] for item in best_itinerary])
            if current_last < best_last:
                best_itinerary = itinerary

    result = {"itinerary": []}
    for item in best_itinerary:
        result["itinerary"].append({
            "action": "meet",
            "location": item['location'],
            "person": item['person'],
            "start_time": time_to_str(item['start']).replace(':00', ':0') if item['start'] % 60 == 0 else time_to_str(item['start']),
            "end_time": time_to_str(item['end']).replace(':00', ':0') if item['end'] % 60 == 0 else time_to_str(item['end'])
        })

    print(json.dumps(result))

if __name__ == "__main__":
    main()