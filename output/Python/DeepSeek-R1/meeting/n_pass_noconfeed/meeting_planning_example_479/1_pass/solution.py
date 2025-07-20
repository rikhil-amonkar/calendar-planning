import itertools
import json

def main():
    travel_times = {
        "Embarcadero": {"Golden Gate Park": 25, "Haight-Ashbury": 21, "Bayview": 21, "Presidio": 20, "Financial District": 5},
        "Golden Gate Park": {"Embarcadero": 25, "Haight-Ashbury": 7, "Bayview": 23, "Presidio": 11, "Financial District": 26},
        "Haight-Ashbury": {"Embarcadero": 20, "Golden Gate Park": 7, "Bayview": 18, "Presidio": 15, "Financial District": 21},
        "Bayview": {"Embarcadero": 19, "Golden Gate Park": 22, "Haight-Ashbury": 19, "Presidio": 31, "Financial District": 19},
        "Presidio": {"Embarcadero": 20, "Golden Gate Park": 12, "Haight-Ashbury": 15, "Bayview": 31, "Financial District": 23},
        "Financial District": {"Embarcadero": 4, "Golden Gate Park": 23, "Haight-Ashbury": 19, "Bayview": 19, "Presidio": 22}
    }
    
    friends = [
        {"name": "Mary", "location": "Golden Gate Park", "start": 525, "end": 705, "duration": 45},
        {"name": "Kevin", "location": "Haight-Ashbury", "start": 615, "end": 975, "duration": 90},
        {"name": "Deborah", "location": "Bayview", "start": 900, "end": 1155, "duration": 120},
        {"name": "Stephanie", "location": "Presidio", "start": 600, "end": 1035, "duration": 120},
        {"name": "Emily", "location": "Financial District", "start": 690, "end": 1305, "duration": 105}
    ]
    
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    start_time = 540
    start_location = "Embarcadero"
    found = False
    best_schedule = None
    
    for size in range(5, 0, -1):
        for subset in itertools.combinations(friends, size):
            perms = itertools.permutations(subset)
            for perm in perms:
                current_time = start_time
                current_location = start_location
                temp_schedule = []
                valid_perm = True
                for friend in perm:
                    if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
                        valid_perm = False
                        break
                    travel_duration = travel_times[current_location][friend['location']]
                    arrival_time = current_time + travel_duration
                    start_meeting = max(arrival_time, friend['start'])
                    end_meeting = start_meeting + friend['duration']
                    if end_meeting > friend['end']:
                        valid_perm = False
                        break
                    temp_schedule.append({
                        'friend': friend,
                        'start': start_meeting,
                        'end': end_meeting
                    })
                    current_time = end_meeting
                    current_location = friend['location']
                if valid_perm:
                    best_schedule = temp_schedule
                    found = True
                    break
            if found:
                break
        if found:
            break
    
    itinerary = []
    if best_schedule is not None:
        for meeting in best_schedule:
            friend_info = meeting['friend']
            itinerary.append({
                "action": "meet",
                "location": friend_info['location'],
                "person": friend_info['name'],
                "start_time": format_time(meeting['start']),
                "end_time": format_time(meeting['end'])
            })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()