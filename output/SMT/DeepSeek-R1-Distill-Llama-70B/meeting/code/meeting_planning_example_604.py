import itertools
from z3 import *

# Define travel times between locations
travel_times = {
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'North Beach'): 20,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'North Beach'): 5,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'North Beach'): 8,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'North Beach'): 15,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Alamo Square'): 16,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Laura',
        'location': 'The Castro',
        'start': 1260,  # 7:45 PM
        'end': 1410,    # 9:30 PM
        'duration': 105
    },
    {
        'name': 'Daniel',
        'location': 'Golden Gate Park',
        'start': 1715,  # 9:15 PM
        'end': 1785,    # 9:45 PM
        'duration': 15
    },
    {
        'name': 'William',
        'location': 'Embarcadero',
        'start': 420,   # 7:00 AM
        'end': 540,     # 9:00 AM
        'duration': 90
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'start': 810,   # 2:30 PM
        'end': 1365,    # 7:45 PM
        'duration': 30
    },
    {
        'name': 'Stephanie',
        'location': 'Nob Hill',
        'start': 450,   # 7:30 AM
        'end': 570,     # 9:30 AM
        'duration': 45
    },
    {
        'name': 'Joseph',
        'location': 'Alamo Square',
        'start': 690,   # 11:30 AM
        'end': 765,     # 12:45 PM
        'duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'North Beach',
        'start': 1080,  # 3:45 PM
        'end': 1275,    # 7:15 PM
        'duration': 30
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
                if max_met == 7:
                    break  # Cannot do better than meeting all seven

    if best_schedule:
        print("SOLUTION: The optimal schedule meets all seven friends in the following order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()