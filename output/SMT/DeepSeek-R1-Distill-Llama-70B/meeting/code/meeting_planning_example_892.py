import itertools
from z3 import *

# Define travel times between locations (in minutes)
travel_times = {
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Embarcadero'): 14,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Embarcadero'): 19,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Embarcadero'): 30,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Embarcadero'): 19,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Embarcadero'): 5,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Embarcadero'): 6,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Russian Hill'): 8,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Charles',
        'location': 'Bayview',
        'start': 690,   # 11:30 AM
        'end': 870,     # 2:30 PM
        'duration': 45
    },
    {
        'name': 'Robert',
        'location': 'Sunset District',
        'start': 1125,  # 4:45 PM
        'end': 1440,    # 9:00 PM
        'duration': 30
    },
    {
        'name': 'Karen',
        'location': 'Richmond District',
        'start': 1365,  # 7:15 PM
        'end': 1710,    # 9:30 PM
        'duration': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Nob Hill',
        'start': 1065,  # 4:15 PM
        'end': 1350,    # 8:30 PM
        'duration': 90
    },
    {
        'name': 'Margaret',
        'location': 'Chinatown',
        'start': 855,   # 2:15 PM
        'end': 1215,    # 7:45 PM
        'duration': 120
    },
    {
        'name': 'Patricia',
        'location': 'Haight-Ashbury',
        'start': 870,   # 2:30 PM
        'end': 1350,    # 8:30 PM
        'duration': 45
    },
    {
        'name': 'Mark',
        'location': 'North Beach',
        'start': 840,   # 2:00 PM
        'end': 1170,    # 6:30 PM
        'duration': 105
    },
    {
        'name': 'Melissa',
        'location': 'Russian Hill',
        'start': 780,   # 1:00 PM
        'end': 1365,    # 7:45 PM
        'duration': 30
    },
    {
        'name': 'Laura',
        'location': 'Embarcadero',
        'start': 465,   # 7:45 AM
        'end': 810,     # 1:15 PM
        'duration': 105
    }
]

def main():
    max_met = 0
    best_schedule = None

    for perm in itertools.permutations(friends):
        s = Solver()
        var = {}
        for friend in perm:
            var_name = friend['name'] + '_start'
            var[friend['name']] = Real(var_name)

        # Add constraints for each friend's availability
        for friend in perm:
            s.add(var[friend['name']] >= friend['start'])
            s.add(var[friend['name']] + friend['duration'] <= friend['end'])

        # Add constraints for travel times between consecutive friends
        for i in range(len(perm) - 1):
            current = perm[i]
            next_friend = perm[i+1]
            travel = travel_times[(current['location'], next_friend['location'])]
            s.add(var[next_friend['name']] >= var[current['name']] + current['duration'] + travel)

        # Check satisfiability
        if s.check() == sat:
            model = s.model()
            if len(perm) > max_met:
                max_met = len(perm)
                best_schedule = perm
                if max_met == 8:
                    break  # Cannot do better than meeting all eight

    if best_schedule:
        print("SOLUTION: The optimal schedule meets all eight friends in the following order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()