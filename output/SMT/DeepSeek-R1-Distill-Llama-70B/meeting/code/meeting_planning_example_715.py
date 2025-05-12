import itertools
from z3 import *

# Define travel times between locations
travel_times = {
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 9,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Amanda',
        'location': 'Marina District',
        'start': 885,   # 2:45 PM
        'end': 1215,    # 7:30 PM
        'duration': 105
    },
    {
        'name': 'Melissa',
        'location': 'The Castro',
        'start': 570,   # 9:30 AM
        'end': 1020,    # 5:00 PM
        'duration': 30
    },
    {
        'name': 'Jeffrey',
        'location': 'Fisherman\'s Wharf',
        'start': 765,   # 12:45 PM
        'end': 1125,    # 6:45 PM
        'duration': 120
    },
    {
        'name': 'Matthew',
        'location': 'Bayview',
        'start': 615,   # 10:15 AM
        'end': 735,     # 1:15 PM
        'duration': 30
    },
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'start': 1020,  # 5:00 PM
        'end': 1710,    # 9:30 PM
        'duration': 105
    },
    {
        'name': 'Karen',
        'location': 'Mission District',
        'start': 1050,  # 5:30 PM
        'end': 1260,    # 8:30 PM
        'duration': 105
    },
    {
        'name': 'Robert',
        'location': 'Alamo Square',
        'start': 675,   # 11:15 AM
        'end': 990,     # 5:30 PM
        'duration': 120
    },
    {
        'name': 'Joseph',
        'location': 'Golden Gate Park',
        'start': 510,   # 8:30 AM
        'end': 1710,    # 9:15 PM
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