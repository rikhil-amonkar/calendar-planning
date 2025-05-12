import itertools
from z3 import *

# Define travel times between locations
travel_times = {
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'North Beach'): 19,
}

# Define friends' data (time in minutes since midnight)
friends = [
    {
        'name': 'Kimberly',
        'location': 'Presidio',
        'start': 990,   # 3:30 PM
        'end': 1020,    # 4:00 PM
        'duration': 15
    },
    {
        'name': 'Elizabeth',
        'location': 'Alamo Square',
        'start': 1125,  # 7:15 PM
        'end': 1200,    # 8:15 PM
        'duration': 15
    },
    {
        'name': 'Joshua',
        'location': 'Marina District',
        'start': 630,   # 10:30 AM
        'end': 900,     # 2:15 PM
        'duration': 45
    },
    {
        'name': 'Sandra',
        'location': 'Financial District',
        'start': 1170,  # 7:30 PM
        'end': 1200,    # 8:15 PM
        'duration': 45
    },
    {
        'name': 'Kenneth',
        'location': 'Nob Hill',
        'start': 765,   # 12:45 PM
        'end': 2175,    # 9:45 PM
        'duration': 30
    },
    {
        'name': 'Betty',
        'location': 'Sunset District',
        'start': 840,   # 2:00 PM
        'end': 1260,    # 7:00 PM
        'duration': 60
    },
    {
        'name': 'Deborah',
        'location': 'Chinatown',
        'start': 1035,  # 5:15 PM
        'end': 1260,    # 8:30 PM
        'duration': 15
    },
    {
        'name': 'Barbara',
        'location': 'Russian Hill',
        'start': 1050,  # 5:30 PM
        'end': 1350,    # 9:15 PM
        'duration': 120
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'start': 1125,  # 5:45 PM
        'end': 1350,    # 8:45 PM
        'duration': 90
    },
    {
        'name': 'Daniel',
        'location': 'Haight-Ashbury',
        'start': 1170,  # 6:30 PM
        'end': 1185,    # 6:45 PM
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
                if max_met == 9:
                    break  # Cannot do better than meeting all nine

    if best_schedule:
        print("SOLUTION: The optimal schedule meets the following friends in this order:")
        print(" -> ".join([f['name'] for f in best_schedule]))
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()