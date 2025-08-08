from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Mission District'): 26,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Bayview', 'Presidio'): 31,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Mission District'): 13,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Bayview'): 22,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Mission District'): 18,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Bayview'): 22,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Mission District'): 18,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'North Beach'): 17,
    }

    # Friends' availability and meeting constraints
    friends = {
        'Jessica': {
            'location': 'Golden Gate Park',
            'available_start': (13, 45),  # 1:45 PM
            'available_end': (15, 0),      # 3:00 PM
            'min_duration': 30,            # minutes
        },
        'Ashley': {
            'location': 'Bayview',
            'available_start': (17, 15),    # 5:15 PM
            'available_end': (20, 0),      # 8:00 PM
            'min_duration': 105,           # minutes
        },
        'Ronald': {
            'location': 'Chinatown',
            'available_start': (7, 15),    # 7:15 AM
            'available_end': (14, 45),      # 2:45 PM
            'min_duration': 90,             # minutes
        },
        'William': {
            'location': 'North Beach',
            'available_start': (13, 15),    # 1:15 PM
            'available_end': (20, 15),      # 8:15 PM
            'min_duration': 15,             # minutes
        },
        'Daniel': {
            'location': 'Mission District',
            'available_start': (7, 0),      # 7:00 AM
            'available_end': (11, 15),      # 11:15 AM
            'min_duration': 105,           # minutes
        }
    }

    # Current location starts at Presidio at 9:00 AM
    current_location = 'Presidio'
    current_time = (9, 0)  # 9:00 AM

    # Convert time to minutes since midnight for easier arithmetic
    def time_to_minutes(time):
        return time[0] * 60 + time[1]

    current_minutes = time_to_minutes(current_time)

    # Define variables for each meeting's start and end times (in minutes since midnight)
    meetings = {}
    for name in friends:
        meetings[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'duration': friends[name]['min_duration'],
            'location': friends[name]['location'],
            'available_start': time_to_minutes(friends[name]['available_start']),
            'available_end': time_to_minutes(friends[name]['available_end']),
        }

    # Constraints for each meeting
    for name in meetings:
        m = meetings[name]
        s.add(m['start'] >= m['available_start'])
        s.add(m['end'] <= m['available_end'])
        s.add(m['end'] == m['start'] + m['duration'])

    # Order of meetings and travel times
    # We need to decide the order in which to meet friends, considering travel times
    # This is a complex combinatorial problem, so we'll use Z3 to find a feasible order

    # To simplify, we'll assume a specific order based on the constraints
    # Priority: Daniel (must meet before 11:15 AM), Ronald (before 2:45 PM), Jessica (1:45-3:00 PM), William, Ashley

    # Let's try meeting Daniel first, then Ronald, then Jessica, then William, then Ashley
    # This is a heuristic; in a real scenario, we'd need to explore all possible orders

    # Meeting Daniel first
    s.add(meetings['Daniel']['start'] >= current_minutes)
    s.add(meetings['Daniel']['end'] <= time_to_minutes((11, 15)))

    # Travel from Daniel's location (Mission District) to next meeting
    next_location = 'Chinatown'  # Ronald
    travel_time = travel_times[(friends['Daniel']['location'], next_location)]
    s.add(meetings['Ronald']['start'] >= meetings['Daniel']['end'] + travel_time)

    # Meeting Ronald
    s.add(meetings['Ronald']['end'] <= time_to_minutes((14, 45)))

    # Travel from Ronald's location (Chinatown) to next meeting (Jessica at Golden Gate Park)
    next_location = 'Golden Gate Park'
    travel_time = travel_times[(friends['Ronald']['location'], next_location)]
    s.add(meetings['Jessica']['start'] >= meetings['Ronald']['end'] + travel_time)

    # Meeting Jessica
    s.add(meetings['Jessica']['end'] <= time_to_minutes((15, 0)))

    # Travel from Jessica's location (Golden Gate Park) to next meeting (William at North Beach)
    next_location = 'North Beach'
    travel_time = travel_times[(friends['Jessica']['location'], next_location)]
    s.add(meetings['William']['start'] >= meetings['Jessica']['end'] + travel_time)

    # Meeting William
    s.add(meetings['William']['end'] <= time_to_minutes((20, 15)))

    # Travel from William's location (North Beach) to next meeting (Ashley at Bayview)
    next_location = 'Bayview'
    travel_time = travel_times[(friends['William']['location'], next_location)]
    s.add(meetings['Ashley']['start'] >= meetings['William']['end'] + travel_time)

    # Meeting Ashley
    s.add(meetings['Ashley']['end'] <= time_to_minutes((20, 0)))

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in ['Daniel', 'Ronald', 'Jessica', 'William', 'Ashley']:
            start = model[meetings[name]['start']].as_long()
            end = model[meetings[name]['end']].as_long()
            start_hh = start // 60
            start_mm = start % 60
            end_hh = end // 60
            end_mm = end % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the scheduling problem
result = solve_scheduling()
print(json.dumps(result, indent=2))