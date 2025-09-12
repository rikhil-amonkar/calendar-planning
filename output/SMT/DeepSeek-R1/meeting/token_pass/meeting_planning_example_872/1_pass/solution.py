from z3 import *
import json

def main():
    # Define travel times between locations
    travel_times = {
        'Presidio': {'Presidio': 0, 'Haight-Ashbury': 15, 'Nob Hill': 18, 'Russian Hill': 14, 'North Beach': 18, 'Chinatown': 21, 'Union Square': 22, 'Embarcadero': 20, 'Financial District': 23, 'Marina District': 11},
        'Haight-Ashbury': {'Presidio': 15, 'Haight-Ashbury': 0, 'Nob Hill': 15, 'Russian Hill': 17, 'North Beach': 19, 'Chinatown': 19, 'Union Square': 19, 'Embarcadero': 20, 'Financial District': 21, 'Marina District': 17},
        'Nob Hill': {'Presidio': 17, 'Haight-Ashbury': 13, 'Nob Hill': 0, 'Russian Hill': 5, 'North Beach': 8, 'Chinatown': 6, 'Union Square': 7, 'Embarcadero': 9, 'Financial District': 9, 'Marina District': 11},
        'Russian Hill': {'Presidio': 14, 'Haight-Ashbury': 17, 'Nob Hill': 5, 'Russian Hill': 0, 'North Beach': 5, 'Chinatown': 9, 'Union Square': 10, 'Embarcadero': 8, 'Financial District': 11, 'Marina District': 7},
        'North Beach': {'Presidio': 17, 'Haight-Ashbury': 18, 'Nob Hill': 7, 'Russian Hill': 4, 'North Beach': 0, 'Chinatown': 6, 'Union Square': 7, 'Embarcadero': 6, 'Financial District': 8, 'Marina District': 9},
        'Chinatown': {'Presidio': 19, 'Haight-Ashbury': 19, 'Nob Hill': 9, 'Russian Hill': 7, 'North Beach': 3, 'Chinatown': 0, 'Union Square': 7, 'Embarcadero': 5, 'Financial District': 5, 'Marina District': 12},
        'Union Square': {'Presidio': 24, 'Haight-Ashbury': 18, 'Nob Hill': 9, 'Russian Hill': 13, 'North Beach': 10, 'Chinatown': 7, 'Union Square': 0, 'Embarcadero': 11, 'Financial District': 9, 'Marina District': 18},
        'Embarcadero': {'Presidio': 20, 'Haight-Ashbury': 21, 'Nob Hill': 10, 'Russian Hill': 8, 'North Beach': 5, 'Chinatown': 7, 'Union Square': 10, 'Embarcadero': 0, 'Financial District': 5, 'Marina District': 12},
        'Financial District': {'Presidio': 22, 'Haight-Ashbury': 19, 'Nob Hill': 8, 'Russian Hill': 11, 'North Beach': 7, 'Chinatown': 5, 'Union Square': 9, 'Embarcadero': 4, 'Financial District': 0, 'Marina District': 15},
        'Marina District': {'Presidio': 10, 'Haight-Ashbury': 16, 'Nob Hill': 12, 'Russian Hill': 8, 'North Beach': 11, 'Chinatown': 15, 'Union Square': 16, 'Embarcadero': 14, 'Financial District': 17, 'Marina District': 0}
    }
    
    # Define meetings data (including dummy start meeting)
    meetings = [
        {'name': 'start', 'location': 'Presidio', 'start_min': 540, 'end_min': 540, 'min_duration': 0},
        {'name': 'Karen', 'location': 'Haight-Ashbury', 'start_min': 1260, 'end_min': 1305, 'min_duration': 45},
        {'name': 'Jessica', 'location': 'Nob Hill', 'start_min': 825, 'end_min': 1260, 'min_duration': 90},
        {'name': 'Brian', 'location': 'Russian Hill', 'start_min': 990, 'end_min': 1305, 'min_duration': 60},
        {'name': 'Kenneth', 'location': 'North Beach', 'start_min': 585, 'end_min': 1260, 'min_duration': 30},
        {'name': 'Jason', 'location': 'Chinatown', 'start_min': 495, 'end_min': 705, 'min_duration': 75},
        {'name': 'Stephanie', 'location': 'Union Square', 'start_min': 1005, 'end_min': 1185, 'min_duration': 105},
        {'name': 'Kimberly', 'location': 'Embarcadero', 'start_min': 585, 'end_min': 1170, 'min_duration': 75},
        {'name': 'Steven', 'location': 'Financial District', 'start_min': 435, 'end_min': 1275, 'min_duration': 60},
        {'name': 'Mark', 'location': 'Marina District', 'start_min': 615, 'end_min': 780, 'min_duration': 75}
    ]
    
    n = len(meetings)
    s = Optimize()
    
    # Create Z3 variables for each meeting
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start = [Real(f"start_{i}") for i in range(n)]
    end = [Real(f"end_{i}") for i in range(n)]
    
    # Fix dummy meeting (always meet at 9:00 AM at Presidio)
    s.add(meet[0] == True)
    s.add(start[0] == 540)
    s.add(end[0] == 540)
    
    # Add constraints for each real meeting
    for i in range(1, n):
        # If meeting is attended, enforce time constraints
        s.add(Implies(meet[i], start[i] >= meetings[i]['start_min']))
        s.add(Implies(meet[i], end[i] <= meetings[i]['end_min']))
        s.add(Implies(meet[i], end[i] - start[i] >= meetings[i]['min_duration']))
    
    # Add travel constraints between all pairs of meetings
    for i in range(n):
        for j in range(i+1, n):
            loc_i = meetings[i]['location']
            loc_j = meetings[j]['location']
            travel_ij = travel_times[loc_i][loc_j]
            travel_ji = travel_times[loc_j][loc_i]
            
            # If both meetings are attended, they must not overlap and include travel time
            s.add(Implies(And(meet[i], meet[j]),
                          Or(start[i] >= end[j] + travel_ji, 
                             start[j] >= end[i] + travel_ij)))
    
    # Maximize number of meetings attended (excluding dummy)
    objective = Sum([If(meet[i], 1, 0) for i in range(1, n)])
    s.maximize(objective)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Collect all attended meetings (excluding dummy)
        for i in range(1, n):
            if is_true(m.evaluate(meet[i])):
                start_val = m.evaluate(start[i])
                end_val = m.evaluate(end[i])
                # Convert Z3 values to integers
                start_min = int(str(start_val).split('.')[0])
                end_min = int(str(end_val).split('.')[0])
                # Convert minutes to time string
                start_str = f"{start_min//60}:{start_min%60:02d}"
                end_str = f"{end_min//60}:{end_min%60:02d}"
                itinerary.append({
                    'action': 'meet',
                    'location': meetings[i]['location'],
                    'person': meetings[i]['name'],
                    'start_time': start_str,
                    'end_time': end_str
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()