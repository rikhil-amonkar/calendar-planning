import itertools
from z3 import *

# Define travel times between locations
travel_times = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Emily',
        'location': 'Alamo Square',
        'start': 705,   # 11:45 AM
        'end': 885,     # 3:15 PM
        'duration': 105
    },
    {
        'name': 'Barbara',
        'location': 'Union Square',
        'start': 1080,  # 4:45 PM
        'end': 1170,    # 6:15 PM
        'duration': 60
    },
    {
        'name': 'William',
        'location': 'Chinatown',
        'start': 990,   # 5:15 PM
        'end': 1260,    # 7:00 PM
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
                if max_met == 3:
                    break  # Cannot do better than meeting all three

    if best_schedule:
        print("SOLUTION: The optimal schedule meets all three friends in the following order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()