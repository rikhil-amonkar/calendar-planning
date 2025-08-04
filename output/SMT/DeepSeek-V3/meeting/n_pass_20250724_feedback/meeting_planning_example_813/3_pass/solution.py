from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define travel times (in minutes) between districts
    travel_times = {
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Mission District'): 20,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Mission District'): 20,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Mission District'): 13,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Sunset District'): 27,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Mission District'): 14,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Mission District'): 17,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 25,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Mission District'): 17,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'Embarcadero'): 19,
        ('Mission District', 'Bayview'): 14,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Financial District'): 15,
        ('Mission District', 'Haight-Ashbury'): 12,
    }

    # Friends' availability and constraints
    friends = {
        'Joshua': {'location': 'Embarcadero', 'start': 9*60 + 45, 'end': 18*60, 'duration': 105},
        'Jeffrey': {'location': 'Bayview', 'start': 9*60 + 45, 'end': 20*60 + 15, 'duration': 75},
        'Charles': {'location': 'Union Square', 'start': 10*60 + 45, 'end': 20*60 + 15, 'duration': 120},
        'Joseph': {'location': 'Chinatown', 'start': 7*60, 'end': 15*60 + 30, 'duration': 60},
        'Elizabeth': {'location': 'Sunset District', 'start': 9*60, 'end': 9*60 + 45, 'duration': 45},
        'Matthew': {'location': 'Golden Gate Park', 'start': 11*60, 'end': 19*60 + 30, 'duration': 45},
        'Carol': {'location': 'Financial District', 'start': 10*60 + 45, 'end': 11*60 + 15, 'duration': 15},
        'Paul': {'location': 'Haight-Ashbury', 'start': 19*60 + 15, 'end': 20*60 + 30, 'duration': 15},
        'Rebecca': {'location': 'Mission District', 'start': 17*60, 'end': 21*60 + 45, 'duration': 45},
    }

    # Variables for each meeting's start and end times
    meetings = {}
    for name in friends:
        meetings[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'location': friends[name]['location'],
        }
        s.add(meetings[name]['start'] >= friends[name]['start'])
        s.add(meetings[name]['end'] <= friends[name]['end'])
        s.add(meetings[name]['end'] == meetings[name]['start'] + friends[name]['duration'])

    # Initial location is Marina District at 9:00 AM (540 minutes)
    current_time = 540
    current_location = 'Marina District'

    # Order of meetings (to be determined by the solver)
    meeting_order = [name for name in friends]
    meeting_vars = [meetings[name]['start'] for name in meeting_order]

    # Ensure meetings don't overlap and account for travel time
    for i in range(len(meeting_order)):
        for j in range(i + 1, len(meeting_order)):
            name1 = meeting_order[i]
            name2 = meeting_order[j]
            loc1 = meetings[name1]['location']
            loc2 = meetings[name2]['location']
            travel = travel_times.get((loc1, loc2), 0)
            s.add(Or(
                meetings[name1]['end'] + travel <= meetings[name2]['start'],
                meetings[name2]['end'] + travel <= meetings[name1]['start'],
            ))

    # Ensure the first meeting is after travel from Marina District
    for name in meeting_order:
        loc = meetings[name]['location']
        travel = travel_times.get((current_location, loc), 0)
        s.add(meetings[name]['start'] >= current_time + travel)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in meeting_order:
            start = m[meetings[name]['start']].as_long()
            end = m[meetings[name]['end']].as_long()
            start_time = f"{start // 60:02d}:{start % 60:02d}"
            end_time = f"{end // 60:02d}:{end % 60:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time,
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))