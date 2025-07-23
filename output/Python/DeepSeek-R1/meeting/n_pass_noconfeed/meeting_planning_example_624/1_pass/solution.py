import itertools
import json

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_time = {
        "Golden Gate Park": {
            "Haight-Ashbury": 7,
            "Fisherman's Wharf": 24,
            "The Castro": 13,
            "Chinatown": 23,
            "Alamo Square": 10,
            "North Beach": 24,
            "Russian Hill": 19
        },
        "Haight-Ashbury": {
            "Golden Gate Park": 7,
            "Fisherman's Wharf": 23,
            "The Castro": 6,
            "Chinatown": 19,
            "Alamo Square": 5,
            "North Beach": 19,
            "Russian Hill": 17
        },
        "Fisherman's Wharf": {
            "Golden Gate Park": 25,
            "Haight-Ashbury": 22,
            "The Castro": 26,
            "Chinatown": 12,
            "Alamo Square": 20,
            "North Beach": 6,
            "Russian Hill": 7
        },
        "The Castro": {
            "Golden Gate Park": 11,
            "Haight-Ashbury": 6,
            "Fisherman's Wharf": 24,
            "Chinatown": 20,
            "Alamo Square": 8,
            "North Beach": 20,
            "Russian Hill": 18
        },
        "Chinatown": {
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Fisherman's Wharf": 8,
            "The Castro": 22,
            "Alamo Square": 17,
            "North Beach": 3,
            "Russian Hill": 7
        },
        "Alamo Square": {
            "Golden Gate Park": 9,
            "Haight-Ashbury": 5,
            "Fisherman's Wharf": 19,
            "The Castro": 8,
            "Chinatown": 16,
            "North Beach": 15,
            "Russian Hill": 13
        },
        "North Beach": {
            "Golden Gate Park": 22,
            "Haight-Ashbury": 18,
            "Fisherman's Wharf": 5,
            "The Castro": 22,
            "Chinatown": 6,
            "Alamo Square": 16,
            "Russian Hill": 4
        },
        "Russian Hill": {
            "Golden Gate Park": 21,
            "Haight-Ashbury": 17,
            "Fisherman's Wharf": 7,
            "The Castro": 21,
            "Chinatown": 9,
            "Alamo Square": 15,
            "North Beach": 5
        }
    }
    
    friends_info = [
        {'name': 'Carol', 'location': 'Haight-Ashbury', 'available_start': 1290, 'available_end': 1350, 'min_duration': 60},
        {'name': 'Laura', 'location': "Fisherman's Wharf", 'available_start': 705, 'available_end': 1290, 'min_duration': 60},
        {'name': 'Karen', 'location': 'The Castro', 'available_start': 435, 'available_end': 840, 'min_duration': 75},
        {'name': 'Elizabeth', 'location': 'Chinatown', 'available_start': 735, 'available_end': 1290, 'min_duration': 75},
        {'name': 'Deborah', 'location': 'Alamo Square', 'available_start': 720, 'available_end': 900, 'min_duration': 105},
        {'name': 'Jason', 'location': 'North Beach', 'available_start': 885, 'available_end': 1140, 'min_duration': 90},
        {'name': 'Steven', 'location': 'Russian Hill', 'available_start': 885, 'available_end': 1110, 'min_duration': 120}
    ]
    
    n = len(friends_info)
    best_schedule = None
    found = False
    
    for size in range(n, 0, -1):
        for indices in itertools.combinations(range(n), size):
            subset = [friends_info[i] for i in indices]
            for perm in itertools.permutations(subset):
                current_location = "Golden Gate Park"
                current_time = 540
                scheduled_meetings = []
                valid = True
                for friend in perm:
                    t = travel_time[current_location][friend['location']]
                    arrival_time = current_time + t
                    start_meeting = max(arrival_time, friend['available_start'])
                    if start_meeting + friend['min_duration'] <= friend['available_end']:
                        end_meeting = start_meeting + friend['min_duration']
                        scheduled_meetings.append((friend, start_meeting, end_meeting))
                        current_location = friend['location']
                        current_time = end_meeting
                    else:
                        valid = False
                        break
                if valid:
                    best_schedule = scheduled_meetings
                    found = True
                    break
            if found:
                break
        if found:
            break
    
    itinerary = []
    if best_schedule:
        for meeting in best_schedule:
            friend = meeting[0]
            start_time_str = min_to_time(meeting[1])
            end_time_str = min_to_time(meeting[2])
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()