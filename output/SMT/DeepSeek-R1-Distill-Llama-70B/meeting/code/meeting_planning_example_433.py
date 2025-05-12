import itertools
from z3 import *

# Define travel times between locations (in minutes)
travel_times = {
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Golden Gate Park'): 23,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 20,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Emily',
        'location': 'Richmond District',
        'start': 1260,  # 7:00 PM
        'end': 1440,    # 9:00 PM
        'duration': 15
    },
    {
        'name': 'Margaret',
        'location': 'Financial District',
        'start': 990,   # 4:30 PM
        'end': 1230,    # 8:15 PM
        'duration': 75
    },
    {
        'name': 'Ronald',
        'location': 'North Beach',
        'start': 1170,  # 6:30 PM
        'end': 1260,    # 7:30 PM
        'duration': 45
    },
    {
        'name': 'Deborah',
        'location': 'The Castro',
        'start': 810,   # 1:45 PM
        'end': 1710,    # 9:15 PM
        'duration': 90
    },
    {
        'name': 'Jeffrey',
        'location': 'Golden Gate Park',
        'start': 690,   # 11:15 AM
        'end': 930,     # 2:30 PM
        'duration': 120
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