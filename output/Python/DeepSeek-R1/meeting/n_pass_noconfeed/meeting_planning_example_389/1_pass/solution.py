import itertools
import json

def main():
    friends = [
        {'name': 'Sarah', 'location': "Fisherman's Wharf", 'start': 345, 'end': 510, 'min_duration': 105},
        {'name': 'Mary', 'location': 'Richmond District', 'start': 240, 'end': 615, 'min_duration': 75},
        {'name': 'Helen', 'location': 'Mission District', 'start': 765, 'end': 810, 'min_duration': 30},
        {'name': 'Thomas', 'location': 'Bayview', 'start': 375, 'end': 585, 'min_duration': 120}
    ]
    
    loc_to_index = {
        "Haight-Ashbury": 0,
        "Fisherman's Wharf": 1,
        "Richmond District": 2,
        "Mission District": 3,
        "Bayview": 4
    }
    
    travel_times = [
        [0, 23, 10, 11, 18],
        [22, 0, 18, 22, 26],
        [10, 18, 0, 20, 26],
        [12, 22, 20, 0, 15],
        [19, 25, 25, 13, 0]
    ]
    
    def format_time(minutes_after_9am):
        total_minutes = 9 * 60 + minutes_after_9am
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h}:{m:02d}"
    
    n = len(friends)
    best_schedule = None
    
    for k in range(n, 0, -1):
        best_candidate = None
        for subset in itertools.combinations(friends, k):
            total_meeting_time = sum(f['min_duration'] for f in subset)
            found = False
            for perm in itertools.permutations(subset):
                current_loc = 0
                current_time = 0
                schedule = []
                valid = True
                for friend in perm:
                    loc_idx = loc_to_index[friend['location']]
                    travel_time = travel_times[current_loc][loc_idx]
                    current_time += travel_time
                    if current_time < friend['start']:
                        current_time = friend['start']
                    if current_time + friend['min_duration'] > friend['end']:
                        valid = False
                        break
                    end_time = current_time + friend['min_duration']
                    schedule.append({
                        'action': 'meet',
                        'location': friend['location'],
                        'person': friend['name'],
                        'start_time': format_time(current_time),
                        'end_time': format_time(end_time)
                    })
                    current_time = end_time
                    current_loc = loc_idx
                if valid:
                    found = True
                    break
            if found:
                if best_candidate is None or total_meeting_time > best_candidate[1]:
                    best_candidate = (schedule, total_meeting_time)
        if best_candidate is not None:
            best_schedule = best_candidate[0]
            break
    
    if best_schedule is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": best_schedule}
    
    print(json.dumps(result))

if __name__ == '__main__':
    main()