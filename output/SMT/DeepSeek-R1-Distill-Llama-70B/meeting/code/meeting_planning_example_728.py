import itertools
from z3 import *

# Define travel times between locations
travel_times = {
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Russian Hill'): 15,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Russian Hill'): 13,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Russian Hill'): 24,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Russian Hill'): 11,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Haight-Ashbury'): 17,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Karen',
        'location': 'Mission District',
        'start': 855,   # 2:15 PM
        'end': 1500,    # 10:00 PM
        'duration': 30
    },
    {
        'name': 'Richard',
        'location': 'Fisherman\'s Wharf',
        'start': 870,   # 2:30 PM
        'end': 1050,    # 5:30 PM
        'duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Presidio',
        'start': 1785,  # 9:45 PM
        'end': 1845,    # 10:45 PM
        'duration': 60
    },
    {
        'name': 'Joseph',
        'location': 'Union Square',
        'start': 705,   # 11:45 AM
        'end': 990,     # 2:45 PM
        'duration': 120
    },
    {
        'name': 'Helen',
        'location': 'Sunset District',
        'start': 885,   # 2:45 PM
        'end': 1305,    # 8:45 PM
        'duration': 105
    },
    {
        'name': 'Elizabeth',
        'location': 'Financial District',
        'start': 600,   # 10:00 AM
        'end': 765,     # 12:45 PM
        'duration': 75
    },
    {
        'name': 'Kimberly',
        'location': 'Haight-Ashbury',
        'start': 855,   # 2:15 PM
        'end': 1050,    # 5:30 PM
        'duration': 105
    },
    {
        'name': 'Ashley',
        'location': 'Russian Hill',
        'start': 690,   # 11:30 AM
        'end': 1710,    # 9:30 PM
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
                if max_met == 8:
                    break  # Cannot do better than meeting all eight

    if best_schedule:
        print("SOLUTION: The optimal schedule meets all eight friends in the following order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()