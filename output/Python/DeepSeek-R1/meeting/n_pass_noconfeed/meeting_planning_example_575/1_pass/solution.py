import itertools
import json

def main():
    travel_time_dict = {
        "The Castro": {"Presidio": 20, "Sunset District": 17, "Haight-Ashbury": 6, "Mission District": 7, "Golden Gate Park": 11, "Russian Hill": 18},
        "Presidio": {"The Castro": 21, "Sunset District": 15, "Haight-Ashbury": 15, "Mission District": 26, "Golden Gate Park": 12, "Russian Hill": 14},
        "Sunset District": {"The Castro": 17, "Presidio": 16, "Haight-Ashbury": 15, "Mission District": 24, "Golden Gate Park": 11, "Russian Hill": 24},
        "Haight-Ashbury": {"The Castro": 6, "Presidio": 15, "Sunset District": 15, "Mission District": 11, "Golden Gate Park": 7, "Russian Hill": 17},
        "Mission District": {"The Castro": 7, "Presidio": 25, "Sunset District": 24, "Haight-Ashbury": 12, "Golden Gate Park": 17, "Russian Hill": 15},
        "Golden Gate Park": {"The Castro": 13, "Presidio": 11, "Sunset District": 10, "Haight-Ashbury": 7, "Mission District": 17, "Russian Hill": 19},
        "Russian Hill": {"The Castro": 21, "Presidio": 14, "Sunset District": 23, "Haight-Ashbury": 17, "Mission District": 16, "Golden Gate Park": 21}
    }

    friends_list = [
        {'name': 'Rebecca', 'location': 'Presidio', 'start': 18*60+15, 'end': 20*60+45, 'min_time': 60},
        {'name': 'Linda', 'location': 'Sunset District', 'start': 15*60+30, 'end': 19*60+45, 'min_time': 30},
        {'name': 'Elizabeth', 'location': 'Haight-Ashbury', 'start': 17*60+15, 'end': 19*60+30, 'min_time': 105},
        {'name': 'William', 'location': 'Mission District', 'start': 13*60+15, 'end': 19*60+30, 'min_time': 30},
        {'name': 'Robert', 'location': 'Golden Gate Park', 'start': 14*60+15, 'end': 21*60+30, 'min_time': 45},
        {'name': 'Mark', 'location': 'Russian Hill', 'start': 10*60+0, 'end': 21*60+15, 'min_time': 75}
    ]

    start_time_minutes = 9 * 60
    start_location = "The Castro"
    found = False
    result_itinerary_minutes = None

    for k in range(len(friends_list), 0, -1):
        for subset in itertools.combinations(friends_list, k):
            for perm in itertools.permutations(subset):
                current_time = start_time_minutes
                current_location = start_location
                itinerary = []
                feasible = True
                for friend in perm:
                    from_loc = current_location
                    to_loc = friend['location']
                    travel_time = travel_time_dict[from_loc][to_loc]
                    arrival_time = current_time + travel_time
                    start_meeting = max(arrival_time, friend['start'])
                    if start_meeting > friend['end'] - friend['min_time']:
                        feasible = False
                        break
                    end_meeting = start_meeting + friend['min_time']
                    if end_meeting > friend['end']:
                        feasible = False
                        break
                    itinerary.append({
                        'location': to_loc,
                        'person': friend['name'],
                        'start_time': start_meeting,
                        'end_time': end_meeting
                    })
                    current_time = end_meeting
                    current_location = to_loc
                if feasible:
                    result_itinerary_minutes = itinerary
                    found = True
                    break
            if found:
                break
        if found:
            break

    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"

    result_itinerary = []
    if result_itinerary_minutes is not None:
        for meeting in result_itinerary_minutes:
            result_itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['person'],
                "start_time": format_time(meeting['start_time']),
                "end_time": format_time(meeting['end_time'])
            })

    output = {"itinerary": result_itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()