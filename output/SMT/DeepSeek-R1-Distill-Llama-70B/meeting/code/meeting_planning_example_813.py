import itertools
from z3 import *

# Define travel times between locations (in minutes)
travel_times = {
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Mission District'): 20,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Mission District'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 25,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Haight-Ashbury'): 12,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Joshua',
        'location': 'Embarcadero',
        'start': 645,   # 9:45 AM
        'end': 1140,    # 6:00 PM
        'duration': 105
    },
    {
        'name': 'Jeffrey',
        'location': 'Bayview',
        'start': 645,   # 9:45 AM
        'end': 1320,    # 8:15 PM
        'duration': 75
    },
    {
        'name': 'Charles',
        'location': 'Union Square',
        'start': 690,   # 10:45 AM
        'end': 1320,    # 8:15 PM
        'duration': 120
    },
    {
        'name': 'Joseph',
        'location': 'Chinatown',
        'start': 420,   # 7:00 AM
        'end': 990,     # 3:30 PM
        'duration': 60
    },
    {
        'name': 'Elizabeth',
        'location': 'Sunset District',
        'start': 540,   # 9:00 AM
        'end': 585,     # 9:45 AM
        'duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Golden Gate Park',
        'start': 660,   # 11:00 AM
        'end': 1350,    # 7:30 PM
        'duration': 45
    },
    {
        'name': 'Carol',
        'location': 'Financial District',
        'start': 690,   # 10:45 AM
        'end': 735,     # 11:15 AM
        'duration': 15
    },
    {
        'name': 'Paul',
        'location': 'Haight-Ashbury',
        'start': 1365,  # 7:15 PM
        'end': 1410,    # 8:30 PM
        'duration': 15
    },
    {
        'name': 'Rebecca',
        'location': 'Mission District',
        'start': 1020,  # 5:00 PM
        'end': 1410,    # 9:45 PM
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