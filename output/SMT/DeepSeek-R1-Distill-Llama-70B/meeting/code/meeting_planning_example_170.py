import itertools
from z3 import *

# Define travel times between locations (in minutes)
travel_times = {
    ('North Beach', 'Union Square'): 10,
    ('North Beach', 'Russian Hill'): 4,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Russian Hill'): 13,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Union Square'): 11,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Emily',
        'location': 'Union Square',
        'start': 960,   # 4:00 PM
        'end': 1035,    # 5:15 PM
        'duration': 45
    },
    {
        'name': 'Margaret',
        'location': 'Russian Hill',
        'start': 1260,  # 7:00 PM
        'end': 1440,    # 9:00 PM
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
                if max_met == 2:
                    break  # Cannot do better than meeting both

    if best_schedule:
        print("SOLUTION: The optimal schedule meets both friends in the following order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()