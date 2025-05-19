import itertools
import json

def main():
    friends = [
        {
            'name': 'Sarah',
            'location': 'Sunset District',
            'available_start': 10 * 60 + 45,
            'available_end': 19 * 60,
            'duration': 30
        },
        {
            'name': 'Richard',
            'location': 'Haight-Ashbury',
            'available_start': 11 * 60 + 45,
            'available_end': 15 * 60 + 45,
            'duration': 90
        },
        {
            'name': 'Elizabeth',
            'location': 'Mission District',
            'available_start': 11 * 60,
            'available_end': 17 * 60 + 15,
            'duration': 120
        },
        {
            'name': 'Michelle',
            'location': 'Golden Gate Park',
            'available_start': 18 * 60 + 15,
            'available_end': 20 * 60 + 45,
            'duration': 90
        }
    ]
    michelle = friends[3]
    non_michelle = friends[:3]

    travel_time = {
        'Richmond District': {'Sunset District': 11, 'Haight-Ashbury': 10, 'Mission District': 20, 'Golden Gate Park': 9},
        'Sunset District': {'Richmond District': 12, 'Haight-Ashbury': 15, 'Mission District': 24, 'Golden Gate Park': 11},
        'Haight-Ashbury': {'Richmond District': 10, 'Sunset District': 15, 'Mission District': 11, 'Golden Gate Park': 7},
        'Mission District': {'Richmond District': 20, 'Sunset District': 24, 'Haight-Ashbury': 12, 'Golden Gate Park': 17},
        'Golden Gate Park': {'Richmond District': 7, 'Sunset District': 10, 'Haight-Ashbury': 7, 'Mission District': 17}
    }

    best_schedule = None

    for perm in itertools.permutations(non_michelle):
        current_location = 'Richmond District'
        current_time = 540
        schedule = []
        valid = True

        for friend in perm:
            if current_location not in travel_time or friend['location'] not in travel_time[current_location]:
                valid = False
                break
            tt = travel_time[current_location][friend['location']]
            arrival_time = current_time + tt
            start = max(arrival_time, friend['available_start'])
            if start + friend['duration'] > friend['available_end']:
                valid = False
                break
            end = start + friend['duration']
            schedule.append({
                'friend': friend,
                'start': start,
                'end': end,
                'location': friend['location']
            })
            current_time = end
            current_location = friend['location']

        if valid:
            if current_location not in travel_time or michelle['location'] not in travel_time[current_location]:
                valid = False
            else:
                tt = travel_time[current_location][michelle['location']]
                arrival_time = current_time + tt
                start = max(arrival_time, michelle['available_start'])
                if start + michelle['duration'] > michelle['available_end']:
                    valid = False
                else:
                    end = start + michelle['duration']
                    schedule.append({
                        'friend': michelle,
                        'start': start,
                        'end': end,
                        'location': michelle['location']
                    })

        if valid:
            itinerary = []
            for entry in schedule:
                start_h = entry['start'] // 60
                start_m = entry['start'] % 60
                end_h = entry['end'] // 60
                end_m = entry['end'] % 60
                start_str = f"{start_h}:{start_m:02d}"
                end_str = f"{end_h}:{end_m:02d}"
                itinerary.append({
                    "action": "meet",
                    "location": entry['location'],
                    "person": entry['friend']['name'],
                    "start_time": start_str,
                    "end_time": end_str
                })
            if best_schedule is None or len(itinerary) > len(best_schedule) or (len(itinerary) == len(best_schedule) and schedule[-1]['end'] < best_schedule[-1]['end']):
                best_schedule = itinerary

    output = {"itinerary": best_schedule} if best_schedule else {"itinerary": []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()