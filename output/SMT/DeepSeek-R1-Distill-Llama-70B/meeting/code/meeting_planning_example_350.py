import itertools
from z3 import *

# Define travel times between locations
travel_times = {
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Financial District'): 13,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Financial District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Haight-Ashbury'): 19,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Mary',
        'location': 'Pacific Heights',
        'start': 600,   # 10:00 AM
        'end': 1140,    # 7:00 PM
        'duration': 45
    },
    {
        'name': 'Lisa',
        'location': 'Mission District',
        'start': 1260,  # 8:30 PM
        'end': 1440,    # 10:00 PM
        'duration': 75
    },
    {
        'name': 'Betty',
        'location': 'Haight-Ashbury',
        'start': 435,   # 7:15 AM
        'end': 1035,    # 5:15 PM
        'duration': 90
    },
    {
        'name': 'Charles',
        'location': 'Financial District',
        'start': 685,   # 11:15 AM
        'end': 900,     # 3:00 PM
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
                if max_met == 4:
                    break  # Cannot do better than meeting all four

    if best_schedule:
        print("SOLUTION: The optimal schedule meets all four friends in the following order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()