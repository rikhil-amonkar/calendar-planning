from z3 import *

# Define travel times between locations (in minutes)
travel_times = {
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Chinatown'): 23,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Kenneth',
        'location': 'Chinatown',
        'start': 720,   # 12:00 PM
        'end': 900,     # 3:00 PM
        'duration': 90
    },
    {
        'name': 'Barbara',
        'location': 'Golden Gate Park',
        'start': 495,   # 8:15 AM
        'end': 1260,    # 7:00 PM
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
                if max_met == 2:
                    break  # Cannot do better than meeting both

    if best_schedule:
        print("SOLUTION: The optimal schedule meets both friends in the following order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()