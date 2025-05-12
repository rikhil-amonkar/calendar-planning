import itertools
from z3 import *

# Define travel times between locations
travel_times = {
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'start': 630,   # 10:30 AM
        'end': 1200,    # 8:00 PM
        'duration': 90
    },
    {
        'name': 'David',
        'location': 'Union Square',
        'start': 855,   # 3:15 PM
        'end': 1050,    # 7:00 PM
        'duration': 45
    },
    {
        'name': 'Sandra',
        'location': 'Pacific Heights',
        'start': 420,   # 7:00 AM
        'end': 1200,    # 8:00 PM
        'duration': 120
    },
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'start': 1110,  # 7:30 PM
        'end': 1140,    # 8:30 PM
        'duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Fisherman\'s Wharf',
        'start': 600,   # 10:00 AM
        'end': 900,     # 3:00 PM
        'duration': 15
    },
    {
        'name': 'Kenneth',
        'location': 'Marina District',
        'start': 645,   # 10:45 AM
        'end': 780,     # 1:00 PM
        'duration': 45
    },
    {
        'name': 'Melissa',
        'location': 'Richmond District',
        'start': 1110,  # 6:15 PM
        'end': 1200,    # 8:00 PM
        'duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'Sunset District',
        'start': 615,   # 10:15 AM
        'end': 1110,    # 6:15 PM
        'duration': 105
    },
    {
        'name': 'Amanda',
        'location': 'Golden Gate Park',
        'start': 465,   # 7:45 AM
        'end': 1140,    # 6:45 PM
        'duration': 15
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