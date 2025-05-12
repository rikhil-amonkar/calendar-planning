import itertools
from z3 import *

# Define travel times between locations (in minutes)
travel_times = {
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Presidio'): 7,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Melissa',
        'location': 'Golden Gate Park',
        'start': 510,   # 8:30 AM
        'end': 1200,    # 8:00 PM
        'duration': 15
    },
    {
        'name': 'Nancy',
        'location': 'Presidio',
        'start': 1365,  # 7:45 PM
        'end': 1440,    # 10:00 PM
        'duration': 105
    },
    {
        'name': 'Emily',
        'location': 'Richmond District',
        'start': 1125,  # 4:45 PM
        'end': 1440,    # 10:00 PM
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
                if max_met == 3:
                    break  # Cannot do better than meeting all three

    if best_schedule:
        print("SOLUTION: The optimal schedule meets all three friends in the following order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()