import itertools
from z3 import *

# Define travel times between locations (in minutes)
travel_times = {
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Financial District'): 21,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Financial District'): 8,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Financial District'): 5,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Financial District'): 22,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Financial District'): 9,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Financial District'): 17,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Financial District'): 23,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Financial District'): 9,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Union Square'): 9,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Steven',
        'location': 'North Beach',
        'start': 990,   # 5:30 PM
        'end': 1260,    # 8:30 PM
        'duration': 15
    },
    {
        'name': 'Sarah',
        'location': 'Golden Gate Park',
        'start': 1020,  # 5:00 PM
        'end': 1215,    # 7:15 PM
        'duration': 75
    },
    {
        'name': 'Brian',
        'location': 'Embarcadero',
        'start': 855,   # 2:15 PM
        'end': 1020,    # 4:00 PM
        'duration': 105
    },
    {
        'name': 'Stephanie',
        'location': 'Haight-Ashbury',
        'start': 615,   # 10:15 AM
        'end': 735,     # 12:15 PM
        'duration': 75
    },
    {
        'name': 'Melissa',
        'location': 'Richmond District',
        'start': 840,   # 2:00 PM
        'end': 1125,    # 7:30 PM
        'duration': 30
    },
    {
        'name': 'Nancy',
        'location': 'Nob Hill',
        'start': 495,   # 8:15 AM
        'end': 765,     # 12:45 PM
        'duration': 90
    },
    {
        'name': 'David',
        'location': 'Marina District',
        'start': 690,   # 11:15 AM
        'end': 810,     # 1:15 PM
        'duration': 120
    },
    {
        'name': 'James',
        'location': 'Presidio',
        'start': 960,   # 3:00 PM
        'end': 1125,    # 6:15 PM
        'duration': 120
    },
    {
        'name': 'Elizabeth',
        'location': 'Union Square',
        'start': 690,   # 11:30 AM
        'end': 1710,    # 9:00 PM
        'duration': 60
    },
    {
        'name': 'Robert',
        'location': 'Financial District',
        'start': 810,   # 1:15 PM
        'end': 990,     # 3:15 PM
        'duration': 45
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
                if max_met == 10:
                    break  # Cannot do better than meeting all ten

    if best_schedule:
        print("SOLUTION: The optimal schedule meets all ten friends in the following order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()