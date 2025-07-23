import itertools
import json

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    travel_times = {
        "Bayview": {
            "North Beach": 21,
            "Presidio": 31,
            "Haight-Ashbury": 19,
            "Union Square": 17
        },
        "North Beach": {
            "Bayview": 22,
            "Presidio": 17,
            "Haight-Ashbury": 18,
            "Union Square": 7
        },
        "Presidio": {
            "Bayview": 31,
            "North Beach": 18,
            "Haight-Ashbury": 15,
            "Union Square": 22
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "North Beach": 19,
            "Presidio": 15,
            "Union Square": 17
        },
        "Union Square": {
            "Bayview": 15,
            "North Beach": 10,
            "Presidio": 24,
            "Haight-Ashbury": 18
        }
    }
    
    friends = [
        {'name': 'Barbara', 'location': 'North Beach', 'start': 13*60+45, 'end': 20*60+15, 'min_duration': 60},
        {'name': 'Margaret', 'location': 'Presidio', 'start': 10*60+15, 'end': 15*60+15, 'min_duration': 30},
        {'name': 'Kevin', 'location': 'Haight-Ashbury', 'start': 20*60, 'end': 20*60+45, 'min_duration': 30},
        {'name': 'Kimberly', 'location': 'Union Square', 'start': 7*60+45, 'end': 16*60+45, 'min_duration': 30}
    ]
    
    start_time_minutes = 9 * 60
    start_location = "Bayview"
    best_schedule = None
    
    for r in range(4, 0, -1):
        for friend_subset in itertools.combinations(friends, r):
            for perm in itertools.permutations(friend_subset):
                current_location = start_location
                current_time = start_time_minutes
                schedule = []
                valid = True
                
                for friend in perm:
                    travel_duration = travel_times[current_location][friend['location']]
                    arrival_time = current_time + travel_duration
                    start_meeting = max(arrival_time, friend['start'])
                    end_meeting = start_meeting + friend['min_duration']
                    
                    if end_meeting > friend['end']:
                        valid = False
                        break
                    
                    schedule.append({
                        'friend': friend,
                        'start_meeting': start_meeting,
                        'end_meeting': end_meeting
                    })
                    
                    current_location = friend['location']
                    current_time = end_meeting
                
                if valid:
                    best_schedule = schedule
                    break
            if best_schedule is not None:
                break
        if best_schedule is not None:
            break
    
    itinerary = []
    if best_schedule is not None:
        for meet in best_schedule:
            itinerary.append({
                "action": "meet",
                "location": meet['friend']['location'],
                "person": meet['friend']['name'],
                "start_time": minutes_to_time(meet['start_meeting']),
                "end_time": minutes_to_time(meet['end_meeting'])
            })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()