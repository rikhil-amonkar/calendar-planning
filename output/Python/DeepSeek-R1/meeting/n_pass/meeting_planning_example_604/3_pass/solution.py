import json
import itertools

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Corrected symmetric travel times
travel_times = {
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Alamo Square": 20,
        "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 26,
        "Golden Gate Park": 13,
        "Embarcadero": 22,
        "Russian Hill": 18,
        "Nob Hill": 16,
        "Alamo Square": 8,
        "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 25,
        "The Castro": 13,
        "Embarcadero": 25,
        "Russian Hill": 19,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 8,
        "The Castro": 22,
        "Golden Gate Park": 25,
        "Russian Hill": 8,
        "Nob Hill": 10,
        "Alamo Square": 19,
        "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7,
        "The Castro": 18,
        "Golden Gate Park": 19,
        "Embarcadero": 8,
        "Nob Hill": 5,
        "Alamo Square": 15,
        "North Beach": 4
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "The Castro": 16,
        "Golden Gate Park": 20,
        "Embarcadero": 10,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 20,
        "The Castro": 8,
        "Golden Gate Park": 10,
        "Embarcadero": 19,
        "Russian Hill": 15,
        "Nob Hill": 11,
        "North Beach": 16
    },
    "North Beach": {
        "Fisherman's Wharf": 6,
        "The Castro": 20,
        "Golden Gate Park": 24,
        "Embarcadero": 5,
        "Russian Hill": 4,
        "Nob Hill": 8,
        "Alamo Square": 16
    }
}

friends = [
    {'name': 'Joseph', 'location': 'Alamo Square', 'start': 11*60+30, 'end': 12*60+45, 'min_duration': 15},
    {'name': 'Kimberly', 'location': 'North Beach', 'start': 15*60+45, 'end': 19*60+15, 'min_duration': 30},
    {'name': 'Karen', 'location': 'Russian Hill', 'start': 14*60+30, 'end': 19*60+45, 'min_duration': 30},
    {'name': 'Laura', 'location': 'The Castro', 'start': 19*60+45, 'end': 21*60+30, 'min_duration': 105}
]

def main():
    current_location = "Fisherman's Wharf"
    start_time = 9 * 60
    perms = itertools.permutations(friends)
    
    for perm in perms:
        current_loc = current_location
        current_time = start_time
        itinerary = []
        valid = True
        for friend in perm:
            travel_duration = travel_times[current_loc][friend['location']]
            arrival_time = current_time + travel_duration
            start_meeting = max(arrival_time, friend['start'])
            end_meeting = start_meeting + friend['min_duration']
            if end_meeting > friend['end']:
                valid = False
                break
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": minutes_to_time(start_meeting),
                "end_time": minutes_to_time(end_meeting)
            })
            current_loc = friend['location']
            current_time = end_meeting
        if valid:
            result = {"itinerary": itinerary}
            print(json.dumps(result))
            return
    
    current_loc = current_location
    current_time = start_time
    itinerary = []
    for friend in friends:
        travel_duration = travel_times[current_loc][friend['location']]
        arrival_time = current_time + travel_duration
        start_meeting = max(arrival_time, friend['start'])
        end_meeting = start_meeting + friend['min_duration']
        if end_meeting > friend['end']:
            continue
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(start_meeting),
            "end_time": minutes_to_time(end_meeting)
        })
        current_loc = friend['location']
        current_time = end_meeting
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()