import itertools
import json

def main():
    friends = [
        {'name': 'Karen', 'location': 'Russian Hill', 'start': 20*60+45, 'end': 21*60+45, 'duration': 60},
        {'name': 'Jessica', 'location': 'The Castro', 'start': 15*60+45, 'end': 19*60+30, 'duration': 60},
        {'name': 'Matthew', 'location': 'Richmond District', 'start': 7*60+30, 'end': 15*60+15, 'duration': 15},
        {'name': 'Michelle', 'location': 'Marina District', 'start': 10*60+30, 'end': 18*60+45, 'duration': 75},
        {'name': 'Carol', 'location': 'North Beach', 'start': 12*60+0, 'end': 17*60+0, 'duration': 90},
        {'name': 'Stephanie', 'location': 'Union Square', 'start': 10*60+45, 'end': 14*60+15, 'duration': 30},
        {'name': 'Linda', 'location': 'Golden Gate Park', 'start': 10*60+45, 'end': 22*60+0, 'duration': 90},
    ]
    
    travel_time = {
        'Sunset District': {'Russian Hill':24, 'The Castro':17, 'Richmond District':12, 'Marina District':21, 'North Beach':29, 'Union Square':30, 'Golden Gate Park':11},
        'Russian Hill': {'Sunset District':23, 'The Castro':21, 'Richmond District':14, 'Marina District':7, 'North Beach':5, 'Union Square':11, 'Golden Gate Park':21},
        'The Castro': {'Sunset District':17, 'Russian Hill':18, 'Richmond District':16, 'Marina District':21, 'North Beach':20, 'Union Square':19, 'Golden Gate Park':11},
        'Richmond District': {'Sunset District':11, 'Russian Hill':13, 'The Castro':16, 'Marina District':9, 'North Beach':17, 'Union Square':21, 'Golden Gate Park':9},
        'Marina District': {'Sunset District':19, 'Russian Hill':8, 'The Castro':22, 'Richmond District':11, 'North Beach':11, 'Union Square':16, 'Golden Gate Park':18},
        'North Beach': {'Sunset District':27, 'Russian Hill':4, 'The Castro':22, 'Richmond District':18, 'Marina District':9, 'Union Square':7, 'Golden Gate Park':22},
        'Union Square': {'Sunset District':26, 'Russian Hill':13, 'The Castro':19, 'Richmond District':20, 'Marina District':18, 'North Beach':10, 'Golden Gate Park':22},
        'Golden Gate Park': {'Sunset District':10, 'Russian Hill':19, 'The Castro':13, 'Richmond District':7, 'Marina District':16, 'North Beach':24, 'Union Square':22},
    }
    
    best_count = 0
    best_duration = 0
    best_end_time = float('inf')
    best_itinerary = None
    
    for k in range(len(friends), 0, -1):
        for perm in itertools.permutations(friends, k):
            current_loc = 'Sunset District'
            current_time = 9 * 60
            itinerary = []
            valid = True
            for friend in perm:
                to_loc = friend['location']
                try:
                    tt = travel_time[current_loc][to_loc]
                except KeyError:
                    valid = False
                    break
                arrival = current_time + tt
                start = max(arrival, friend['start'])
                latest_start = friend['end'] - friend['duration']
                if start > latest_start:
                    valid = False
                    break
                end = start + friend['duration']
                itinerary.append({'location': to_loc, 'person': friend['name'], 'start_time': start, 'end_time': end})
                current_time = end
                current_loc = to_loc
            if valid:
                count = len(itinerary)
                duration = sum(e['end_time'] - e['start_time'] for e in itinerary)
                end_time = itinerary[-1]['end_time'] if itinerary else 0
                if (count > best_count or
                    (count == best_count and duration > best_duration) or
                    (count == best_count and duration == best_duration and end_time < best_end_time)):
                    best_count = count
                    best_duration = duration
                    best_end_time = end_time
                    best_itinerary = itinerary.copy()
                    if best_count == len(friends):
                        break
            if best_count == len(friends):
                break
        if best_count == len(friends):
            break
    
    if best_itinerary:
        formatted = []
        for event in best_itinerary:
            start_h = event['start_time'] // 60
            start_m = event['start_time'] % 60
            end_h = event['end_time'] // 60
            end_m = event['end_time'] % 60
            formatted.append({
                "action": "meet",
                "location": event['location'],
                "person": event['person'],
                "start_time": f"{start_h}:{start_m:02d}",
                "end_time": f"{end_h}:{end_m:02d}"
            })
        output = {"itinerary": formatted}
    else:
        output = {"itinerary": []}
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()