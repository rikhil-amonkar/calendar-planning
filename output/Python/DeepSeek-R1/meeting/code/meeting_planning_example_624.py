import itertools
import json

def main():
    friends = [
        {'name': 'Carol', 'location': 'Haight-Ashbury', 'available_start': 1290, 'available_end': 1350, 'duration': 60},
        {'name': 'Laura', 'location': 'Fisherman\'s Wharf', 'available_start': 705, 'available_end': 1290, 'duration': 60},
        {'name': 'Karen', 'location': 'The Castro', 'available_start': 435, 'available_end': 840, 'duration': 75},
        {'name': 'Elizabeth', 'location': 'Chinatown', 'available_start': 735, 'available_end': 1290, 'duration': 75},
        {'name': 'Deborah', 'location': 'Alamo Square', 'available_start': 720, 'available_end': 900, 'duration': 105},
        {'name': 'Jason', 'location': 'North Beach', 'available_start': 885, 'available_end': 1140, 'duration': 90},
        {'name': 'Steven', 'location': 'Russian Hill', 'available_start': 885, 'available_end': 1110, 'duration': 120}
    ]
    
    travel_times = {
        'Golden Gate Park': {'Haight-Ashbury':7, 'Fisherman\'s Wharf':24, 'The Castro':13, 'Chinatown':23, 'Alamo Square':10, 'North Beach':24, 'Russian Hill':19},
        'Haight-Ashbury': {'Golden Gate Park':7, 'Fisherman\'s Wharf':23, 'The Castro':6, 'Chinatown':19, 'Alamo Square':5, 'North Beach':19, 'Russian Hill':17},
        'Fisherman\'s Wharf': {'Golden Gate Park':25, 'Haight-Ashbury':22, 'The Castro':26, 'Chinatown':12, 'Alamo Square':20, 'North Beach':6, 'Russian Hill':7},
        'The Castro': {'Golden Gate Park':11, 'Haight-Ashbury':6, 'Fisherman\'s Wharf':24, 'Chinatown':20, 'Alamo Square':8, 'North Beach':20, 'Russian Hill':18},
        'Chinatown': {'Golden Gate Park':23, 'Haight-Ashbury':19, 'Fisherman\'s Wharf':8, 'The Castro':22, 'Alamo Square':17, 'North Beach':3, 'Russian Hill':7},
        'Alamo Square': {'Golden Gate Park':9, 'Haight-Ashbury':5, 'Fisherman\'s Wharf':19, 'The Castro':8, 'Chinatown':16, 'North Beach':15, 'Russian Hill':13},
        'North Beach': {'Golden Gate Park':22, 'Haight-Ashbury':18, 'Fisherman\'s Wharf':5, 'The Castro':22, 'Chinatown':6, 'Alamo Square':16, 'Russian Hill':4},
        'Russian Hill': {'Golden Gate Park':21, 'Haight-Ashbury':17, 'Fisherman\'s Wharf':7, 'The Castro':21, 'Chinatown':9, 'Alamo Square':15, 'North Beach':5}
    }

    max_friends = 0
    best_itinerary = []
    best_end = float('inf')

    for perm in itertools.permutations(friends):
        current_time = 540
        current_loc = 'Golden Gate Park'
        itinerary = []
        valid = True
        count = 0

        for friend in perm:
            try:
                tt = travel_times[current_loc][friend['location']]
            except KeyError:
                break

            arrive = current_time + tt
            start = max(arrive, friend['available_start'])
            end = start + friend['duration']

            if end > friend['available_end']:
                break

            itinerary.append({
                'location': friend['location'],
                'person': friend['name'],
                'start_time': start,
                'end_time': end
            })
            current_time = end
            current_loc = friend['location']
            count += 1

        if count > max_friends or (count == max_friends and current_time < best_end):
            max_friends = count
            best_itinerary = itinerary.copy()
            best_end = current_time

    formatted = []
    for item in best_itinerary:
        def fmt(t):
            h, m = divmod(t, 60)
            return f"{h}:{m:02d}"
        formatted.append({
            "action": "meet",
            "location": item['location'],
            "person": item['person'],
            "start_time": fmt(item['start_time']).lstrip('0'),
            "end_time": fmt(item['end_time']).lstrip('0')
        })

    print(json.dumps({"itinerary": formatted}, indent=2))

if __name__ == "__main__":
    main()