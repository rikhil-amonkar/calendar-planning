import itertools
from z3 import *

# Define travel times between locations
travel_times = {
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Union Square'): 21,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Chinatown'): 16,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'Union Square'): 7,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Union Square'): 9,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Marina District'): 25,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Union Square'): 17,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Bayview'): 15,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Kimberly',
        'location': 'Marina District',
        'start': 855,   # 1:15 PM
        'end': 1065,    # 4:45 PM
        'duration': 15
    },
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'start': 735,   # 12:15 PM
        'end': 1475,    # 8:15 PM
        'duration': 15
    },
    {
        'name': 'Rebecca',
        'location': 'Financial District',
        'start': 855,   # 1:15 PM
        'end': 1065,    # 4:45 PM
        'duration': 75
    },
    {
        'name': 'Margaret',
        'location': 'Bayview',
        'start': 570,   # 9:30 AM
        'end': 810,     # 1:30 PM
        'duration': 30
    },
    {
        'name': 'Kenneth',
        'location': 'Union Square',
        'start': 1410,  # 7:30 PM
        'end': 1530,    # 9:15 PM
        'duration': 75
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
                if max_met == 5:
                    break  # Cannot do better than meeting all five

    if best_schedule:
        print("SOLUTION: The optimal schedule meets all five friends in the following order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()