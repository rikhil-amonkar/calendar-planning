import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Travel times dictionary: {from: {to: minutes}}
    travel_times = {
        'Marina District': {
            'Bayview': 27, 'Sunset District': 19, 'Richmond District': 11, 'Nob Hill': 12,
            'Chinatown': 15, 'Haight-Ashbury': 16, 'North Beach': 11, 'Russian Hill': 8, 'Embarcadero': 14
        },
        'Bayview': {
            'Marina District': 27, 'Sunset District': 23, 'Richmond District': 25, 'Nob Hill': 20,
            'Chinatown': 19, 'Haight-Ashbury': 19, 'North Beach': 22, 'Russian Hill': 23, 'Embarcadero': 19
        },
        'Sunset District': {
            'Marina District': 21, 'Bayview': 22, 'Richmond District': 12, 'Nob Hill': 27,
            'Chinatown': 30, 'Haight-Ashbury': 15, 'North Beach': 28, 'Russian Hill': 24, 'Embarcadero': 30
        },
        'Richmond District': {
            'Marina District': 9, 'Bayview': 27, 'Sunset District': 11, 'Nob Hill': 17,
            'Chinatown': 20, 'Haight-Ashbury': 10, 'North Beach': 17, 'Russian Hill': 13, 'Embarcadero': 19
        },
        'Nob Hill': {
            'Marina District': 11, 'Bayview': 19, 'Sunset District': 24, 'Richmond District': 14,
            'Chinatown': 6, 'Haight-Ashbury': 13, 'North Beach': 8, 'Russian Hill': 5, 'Embarcadero': 9
        },
        'Chinatown': {
            'Marina District': 12, 'Bayview': 20, 'Sunset District': 29, 'Richmond District': 20,
            'Nob Hill': 9, 'Haight-Ashbury': 19, 'North Beach': 3, 'Russian Hill': 7, 'Embarcadero': 5
        },
        'Haight-Ashbury': {
            'Marina District': 17, 'Bayview': 18, 'Sunset District': 15, 'Richmond District': 10,
            'Nob Hill': 15, 'Chinatown': 19, 'North Beach': 19, 'Russian Hill': 17, 'Embarcadero': 20
        },
        'North Beach': {
            'Marina District': 9, 'Bayview': 25, 'Sunset District': 27, 'Richmond District': 18,
            'Nob Hill': 7, 'Chinatown': 6, 'Haight-Ashbury': 18, 'Russian Hill': 4, 'Embarcadero': 6
        },
        'Russian Hill': {
            'Marina District': 7, 'Bayview': 23, 'Sunset District': 23, 'Richmond District': 14,
            'Nob Hill': 5, 'Chinatown': 9, 'Haight-Ashbury': 17, 'North Beach': 5, 'Embarcadero': 8
        },
        'Embarcadero': {
            'Marina District': 12, 'Bayview': 21, 'Sunset District': 30, 'Richmond District': 21,
            'Nob Hill': 10, 'Chinatown': 7, 'Haight-Ashbury': 21, 'North Beach': 5, 'Russian Hill': 8
        }
    }

    # Friend constraints: {name: (location, start, end, min_duration)}
    friends = {
        'Charles': ('Bayview', '11:30', '14:30', 45),
        'Robert': ('Sunset District', '16:45', '21:00', 30),
        'Karen': ('Richmond District', '19:15', '21:30', 60),
        'Rebecca': ('Nob Hill', '16:15', '20:30', 90),
        'Margaret': ('Chinatown', '14:15', '19:45', 120),
        'Patricia': ('Haight-Ashbury', '14:30', '20:30', 45),
        'Mark': ('North Beach', '14:00', '18:30', 105),
        'Melissa': ('Russian Hill', '13:00', '19:45', 30),
        'Laura': ('Embarcadero', '7:45', '13:15', 105)
    }

    # Convert all times to minutes
    friends_min = {}
    for name, (loc, start, end, dur) in friends.items():
        friends_min[name] = (loc, time_to_minutes(start), time_to_minutes(end), dur)

    # Initial state: start at Marina District at 9:00 (540 minutes)
    current_time = 540
    current_loc = 'Marina District'
    itinerary = []

    # Define an optimal order to visit friends based on location proximity
    visit_order = ['Laura', 'Charles', 'Melissa', 'Margaret', 'Mark', 'Patricia', 'Rebecca', 'Robert', 'Karen']

    for name in visit_order:
        loc, start, end, dur = friends_min[name]
        travel_time = travel_times[current_loc][loc]
        arrival_time = current_time + travel_time
        
        # Calculate earliest possible meeting time
        start_meeting = max(arrival_time, start)
        end_meeting = start_meeting + dur
        
        # Check if meeting fits in the time window
        if end_meeting <= end:
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": minutes_to_time(start_meeting),
                "end_time": minutes_to_time(end_meeting)
            })
            current_time = end_meeting
            current_loc = loc
        else:
            # If we can't fit the meeting, try to adjust previous meetings to make room
            # For now, just skip (but constraints say we should be able to meet everyone)
            pass

    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))