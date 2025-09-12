from z3 import *
import json

def main():
    # Define travel time matrix
    travel = {
        'Union Square': {
            'Union Square': 0, 'Presidio': 24, 'Alamo Square': 15, 'Marina District': 18,
            'Financial District': 9, 'Nob Hill': 9, 'Sunset District': 27, 'Chinatown': 7,
            'Russian Hill': 13, 'North Beach': 10, 'Haight-Ashbury': 18
        },
        'Presidio': {
            'Union Square': 22, 'Presidio': 0, 'Alamo Square': 19, 'Marina District': 11,
            'Financial District': 23, 'Nob Hill': 18, 'Sunset District': 15, 'Chinatown': 21,
            'Russian Hill': 14, 'North Beach': 18, 'Haight-Ashbury': 15
        },
        'Alamo Square': {
            'Union Square': 14, 'Presidio': 17, 'Alamo Square': 0, 'Marina District': 15,
            'Financial District': 17, 'Nob Hill': 11, 'Sunset District': 16, 'Chinatown': 15,
            'Russian Hill': 13, 'North Beach': 15, 'Haight-Ashbury': 5
        },
        'Marina District': {
            'Union Square': 16, 'Presidio': 10, 'Alamo Square': 15, 'Marina District': 0,
            'Financial District': 17, 'Nob Hill': 12, 'Sunset District': 19, 'Chinatown': 15,
            'Russian Hill': 8, 'North Beach': 11, 'Haight-Ashbury': 16
        },
        'Financial District': {
            'Union Square': 9, 'Presidio': 22, 'Alamo Square': 17, 'Marina District': 15,
            'Financial District': 0, 'Nob Hill': 8, 'Sunset District': 30, 'Chinatown': 5,
            'Russian Hill': 11, 'North Beach': 7, 'Haight-Ashbury': 19
        },
        'Nob Hill': {
            'Union Square': 7, 'Presidio': 17, 'Alamo Square': 11, 'Marina District': 11,
            'Financial District': 9, 'Nob Hill': 0, 'Sunset District': 24, 'Chinatown': 6,
            'Russian Hill': 5, 'North Beach': 8, 'Haight-Ashbury': 13
        },
        'Sunset District': {
            'Union Square': 30, 'Presidio': 16, 'Alamo Square': 17, 'Marina District': 21,
            'Financial District': 30, 'Nob Hill': 27, 'Sunset District': 0, 'Chinatown': 30,
            'Russian Hill': 24, 'North Beach': 28, 'Haight-Ashbury': 15
        },
        'Chinatown': {
            'Union Square': 7, 'Presidio': 19, 'Alamo Square': 17, 'Marina District': 12,
            'Financial District': 5, 'Nob Hill': 9, 'Sunset District': 29, 'Chinatown': 0,
            'Russian Hill': 7, 'North Beach': 3, 'Haight-Ashbury': 19
        },
        'Russian Hill': {
            'Union Square': 10, 'Presidio': 14, 'Alamo Square': 15, 'Marina District': 7,
            'Financial District': 11, 'Nob Hill': 5, 'Sunset District': 23, 'Chinatown': 9,
            'Russian Hill': 0, 'North Beach': 5, 'Haight-Ashbury': 17
        },
        'North Beach': {
            'Union Square': 7, 'Presidio': 17, 'Alamo Square': 16, 'Marina District': 9,
            'Financial District': 8, 'Nob Hill': 7, 'Sunset District': 27, 'Chinatown': 6,
            'Russian Hill': 4, 'North Beach': 0, 'Haight-Ashbury': 18
        },
        'Haight-Ashbury': {
            'Union Square': 19, 'Presidio': 15, 'Alamo Square': 5, 'Marina District': 17,
            'Financial District': 21, 'Nob Hill': 15, 'Sunset District': 15, 'Chinatown': 19,
            'Russian Hill': 17, 'North Beach': 19, 'Haight-Ashbury': 0
        }
    }
    
    # Define friends data
    friends = [
        {'name': 'Kimberly', 'loc': 'Presidio', 'start_avail': 15*60+30, 'end_avail': 16*60, 'min_dur': 15},
        {'name': 'Elizabeth', 'loc': 'Alamo Square', 'start_avail': 19*60+15, 'end_avail': 20*60+15, 'min_dur': 15},
        {'name': 'Joshua', 'loc': 'Marina District', 'start_avail': 10*60+30, 'end_avail': 14*60+15, 'min_dur': 45},
        {'name': 'Sandra', 'loc': 'Financial District', 'start_avail': 19*60+30, 'end_avail': 20*60+15, 'min_dur': 45},
        {'name': 'Kenneth', 'loc': 'Nob Hill', 'start_avail': 12*60+45, 'end_avail': 21*60+45, 'min_dur': 30},
        {'name': 'Betty', 'loc': 'Sunset District', 'start_avail': 14*60, 'end_avail': 19*60, 'min_dur': 60},
        {'name': 'Deborah', 'loc': 'Chinatown', 'start_avail': 17*60+15, 'end_avail': 20*60+30, 'min_dur': 15},
        {'name': 'Barbara', 'loc': 'Russian Hill', 'start_avail': 17*60+30, 'end_avail': 21*60+15, 'min_dur': 120},
        {'name': 'Steven', 'loc': 'North Beach', 'start_avail': 17*60+45, 'end_avail': 20*60+45, 'min_dur': 90},
        {'name': 'Daniel', 'loc': 'Haight-Ashbury', 'start_avail': 18*60+30, 'end_avail': 18*60+45, 'min_dur': 15}
    ]
    
    n = len(friends)
    meet = [Bool(f'meet_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    before = [[Bool(f'before_{i}_{j}') for j in range(n)] for i in range(n)]
    
    s = Optimize()
    
    # Constraints for each friend's availability and duration
    for i in range(n):
        s.add(Implies(meet[i], start[i] >= friends[i]['start_avail']))
        s.add(Implies(meet[i], end[i] <= friends[i]['end_avail']))
        s.add(Implies(meet[i], end[i] - start[i] >= friends[i]['min_dur']))
    
    # Constraint: travel from start location (Union Square) to each meeting
    for i in range(n):
        t = travel['Union Square'][friends[i]['loc']]
        s.add(Implies(meet[i], start[i] >= 540 + t))
    
    # Constraints for ordering and travel between meetings
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            s.add(Implies(And(meet[i], meet[j]), Or(before[i][j], before[j][i])))
            s.add(Implies(And(meet[i], meet[j]), Not(And(before[i][j], before[j][i]))))
            t = travel[friends[i]['loc']][friends[j]['loc']]
            s.add(Implies(And(meet[i], meet[j], before[i][j]), start[j] >= end[i] + t))
    
    # Objective: maximize number of meetings
    objective = Sum([If(meet[i], 1, 0) for i in range(n)])
    s.maximize(objective)
    
    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        for i in range(n):
            if is_true(m.evaluate(meet[i])):
                start_val = m.evaluate(start[i]).as_long()
                end_val = m.evaluate(end[i]).as_long()
                start_str = f"{start_val//60}:{start_val%60:02d}"
                end_str = f"{end_val//60}:{end_val%60:02d}"
                scheduled_meetings.append({
                    'action': 'meet',
                    'location': friends[i]['loc'],
                    'person': friends[i]['name'],
                    'start_time': start_str,
                    'end_time': end_str
                })
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        result = {'itinerary': scheduled_meetings}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()