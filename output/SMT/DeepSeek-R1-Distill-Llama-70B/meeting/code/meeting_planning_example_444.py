import itertools
from z3 import *

# Define travel times between locations
travel_times = {
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('The Castro', 'Financial District'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Ronald',
        'location': 'Russian Hill',
        'start': 810,   # 1:45 PM
        'end': 1035,    # 5:15 PM
        'duration': 105
    },
    {
        'name': 'Patricia',
        'location': 'Sunset District',
        'start': 555,   # 9:15 AM
        'end': 1200,    # 10:00 PM
        'duration': 60
    },
    {
        'name': 'Laura',
        'location': 'North Beach',
        'start': 750,   # 12:30 PM
        'end': 765,     # 12:45 PM
        'duration': 15
    },
    {
        'name': 'Emily',
        'location': 'The Castro',
        'start': 975,   # 4:15 PM
        'end': 1110,    # 6:30 PM
        'duration': 60
    },
    {
        'name': 'Mary',
        'location': 'Golden Gate Park',
        'start': 900,   # 3:00 PM
        'end': 990,     # 4:30 PM
        'duration': 60
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