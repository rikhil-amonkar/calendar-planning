import itertools
from z3 import *

# Define travel times between locations (in minutes)
travel_times = {
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Pacific Heights'): 16,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'David',
        'location': 'Fisherman\'s Wharf',
        'start': 645,   # 10:45 AM
        'end': 990,     # 3:30 PM
        'duration': 15
    },
    {
        'name': 'Timothy',
        'location': 'Pacific Heights',
        'start': 540,   # 9:00 AM
        'end': 990,     # 3:30 PM
        'duration': 75
    },
    {
        'name': 'Robert',
        'location': 'Mission District',
        'start': 735,   # 12:15 PM
        'end': 1365,    # 7:45 PM
        'duration': 90
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