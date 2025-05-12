import itertools
from z3 import *

# Define travel times between locations
travel_times = {
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Union Square'): 22,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Union Square'): 21,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Union Square'): 7,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Union Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Jason',
        'location': 'Richmond District',
        'start': 780,   # 1:00 PM
        'end': 1260,    # 8:45 PM
        'duration': 90
    },
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'start': 1245,  # 6:45 PM
        'end': 1350,    # 8:15 PM
        'duration': 45
    },
    {
        'name': 'Brian',
        'location': 'Financial District',
        'start': 585,   # 9:45 AM
        'end': 1785,    # 9:45 PM
        'duration': 15
    },
    {
        'name': 'Elizabeth',
        'location': 'Golden Gate Park',
        'start': 525,   # 8:45 AM
        'end': 1710,    # 9:30 PM
        'duration': 105
    },
    {
        'name': 'Laura',
        'location': 'Union Square',
        'start': 855,   # 2:15 PM
        'end': 1125,    # 7:30 PM
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