import itertools
from z3 import *

# Define travel times between locations
travel_times = {
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Richmond District'): 11,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Richmond District'): 21,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Richmond District'): 20,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Richmond District'): 12,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Richmond District'): 21,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Richmond District'): 20,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Chinatown'): 20,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Jeffrey',
        'location': 'Fisherman\'s Wharf',
        'start': 615,   # 10:15 AM
        'end': 780,     # 1:00 PM
        'duration': 90
    },
    {
        'name': 'Ronald',
        'location': 'Alamo Square',
        'start': 465,   # 7:45 AM
        'end': 885,     # 2:45 PM
        'duration': 120
    },
    {
        'name': 'Jason',
        'location': 'Financial District',
        'start': 645,   # 10:45 AM
        'end': 960,     # 4:00 PM
        'duration': 105
    },
    {
        'name': 'Melissa',
        'location': 'Union Square',
        'start': 1125,  # 5:45 PM
        'end': 1140,    # 6:15 PM
        'duration': 15
    },
    {
        'name': 'Elizabeth',
        'location': 'Sunset District',
        'start': 885,   # 2:45 PM
        'end': 1050,    # 5:30 PM
        'duration': 105
    },
    {
        'name': 'Margaret',
        'location': 'Embarcadero',
        'start': 810,   # 1:15 PM
        'end': 1260,    # 7:00 PM
        'duration': 90
    },
    {
        'name': 'George',
        'location': 'Golden Gate Park',
        'start': 1260,  # 7:00 PM
        'end': 1440,    # 10:00 PM
        'duration': 75
    },
    {
        'name': 'Richard',
        'location': 'Chinatown',
        'start': 570,   # 9:30 AM
        'end': 1710,    # 9:00 PM
        'duration': 15
    },
    {
        'name': 'Laura',
        'location': 'Richmond District',
        'start': 585,   # 9:45 AM
        'end': 1080,    # 6:00 PM
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
                if max_met == 9:
                    break  # Cannot do better than meeting all nine

    if best_schedule:
        print("SOLUTION: The optimal schedule meets all nine friends in the following order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()