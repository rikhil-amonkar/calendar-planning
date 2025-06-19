import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        'Bayview': {'North Beach': 21, 'Presidio': 31, 'Haight-Ashbury': 19, 'Union Square': 17},
        'North Beach': {'Bayview': 22, 'Presidio': 17, 'Haight-Ashbury': 18, 'Union Square': 7},
        'Presidio': {'Bayview': 31, 'North Beach': 18, 'Haight-Ashbury': 15, 'Union Square': 22},
        'Haight-Ashbury': {'Bayview': 18, 'North Beach': 19, 'Presidio': 15, 'Union Square': 17},
        'Union Square': {'Bayview': 15, 'North Beach': 10, 'Presidio': 24, 'Haight-Ashbury': 18}
    }
    
    friends = [
        {'name': 'Barbara', 'location': 'North Beach', 'start_avail': 13*60+45, 'end_avail': 20*60+15, 'min_duration': 60},
        {'name': 'Margaret', 'location': 'Presidio', 'start_avail': 10*60+15, 'end_avail': 15*60+15, 'min_duration': 30},
        {'name': 'Kevin', 'location': 'Haight-Ashbury', 'start_avail': 20*60, 'end_avail': 20*60+45, 'min_duration': 30},
        {'name': 'Kimberly', 'location': 'Union Square', 'start_avail': 7*60+45, 'end_avail': 16*60+45, 'min_duration': 30}
    ]
    
    start_time = 9*60
    start_location = 'Bayview'
    best_count = 0
    best_itinerary = None
    
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_loc = start_location
        itinerary = []
        count = 0
        valid = True
        for friend in perm:
            travel = travel_times[current_loc][friend['location']]
            current_time += travel
            start_meeting = max(current_time, friend['start_avail'])
            end_meeting = start_meeting + friend['min_duration']
            if end_meeting > friend['end_avail']:
                break
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': start_meeting,
                'end_time': end_meeting
            })
            count += 1
            current_time = end_meeting
            current_loc = friend['location']
            if count == 4:
                best_itinerary = itinerary
                best_count = count
                break
        if best_count == 4:
            break
        if count > best_count:
            best_count = count
            best_itinerary = itinerary
    
    if best_itinerary is None:
        best_itinerary = []
    
    for event in best_itinerary:
        event['start_time'] = minutes_to_time(event['start_time'])
        event['end_time'] = minutes_to_time(event['end_time'])
    
    result = {'itinerary': best_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()