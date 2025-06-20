from z3 import *

# Define the variables
meet_karen = Int('meet_karen')
meet_joseph = Int('meet_joseph')
meet_sandra = Int('meet_sandra')
meet_nancy = Int('meet_nancy')
location_karen = Int('location_karen')
location_joseph = Int('location_joseph')
location_sandra = Int('location_sandra')
location_nancy = Int('location_nancy')

# Define the constraints
travel_times = {
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Marina District'): 18,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Marina District'): 11,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Nob Hill'): 8,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Marina District'): 12,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Chinatown'): 16
}

karen_arrive = 9 * 60 + 15  # 9:15 AM
karen_leave = 9 * 60 + 45   # 9:45 AM
joseph_arrive = 12 * 60 + 30 # 12:30 PM
joseph_leave = 19 * 60 + 45  # 7:45 PM
sandra_arrive = 7 * 60      # 7:00 AM
sandra_leave = 19 * 60       # 7:15 PM
nancy_arrive = 11 * 60      # 11:00 AM
nancy_leave = 20 * 60 + 15  # 8:15 PM

# Define the constraints
s = Solver()

# Karen
s.add(meet_karen >= 30)
s.add(And(Or(location_karen == 0, location_karen == 1, location_karen == 2, location_karen == 3),
          Or(location_karen == 0, location_karen == 1, location_karen == 2, location_karen == 3)))

# Joseph
s.add(meet_joseph >= 90)
s.add(And(Or(location_joseph == 0, location_joseph == 1, location_joseph == 2, location_joseph == 3),
          Or(location_joseph == 0, location_joseph == 1, location_joseph == 2, location_joseph == 3)))

# Sandra
s.add(meet_sandra >= 75)
s.add(And(Or(location_sandra == 0, location_sandra == 1, location_sandra == 2, location_sandra == 3),
          Or(location_sandra == 0, location_sandra == 1, location_sandra == 2, location_sandra == 3)))

# Nancy
s.add(meet_nancy >= 105)
s.add(And(Or(location_nancy == 0, location_nancy == 1, location_nancy == 2, location_nancy == 3),
          Or(location_nancy == 0, location_nancy == 1, location_nancy == 2, location_nancy == 3)))

# Meet exactly 4 people
s.add(Or(meet_karen == 30, meet_joseph == 90, meet_sandra == 75, meet_nancy == 105))
s.add(And(Not(meet_karen == 30), Not(meet_joseph == 90), Not(meet_sandra == 75), Not(meet_nancy == 105)))

# Travel times
locations = ['Union Square', 'Nob Hill', 'Haight-Ashbury', 'Chinatown', 'Marina District']
for i in range(len(locations)):
    for j in range(i + 1, len(locations)):
        start = locations[i]
        end = locations[j]
        if start == 'Union Square':
            s.add(meet_karen + meet_joseph + meet_sandra + meet_nancy >= travel_times[(start, end)])
        else:
            s.add(meet_karen + meet_joseph + meet_sandra + meet_nancy + travel_times[(start, 'Union Square')] >= travel_times[(start, end)])

# Solve the problem
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    if m[meet_karen].as_long() == 30:
        print(f"Meet Karen at {m[location_karen].as_long()}: {m[meet_karen].as_long()} minutes")
    elif m[meet_joseph].as_long() == 90:
        print(f"Meet Joseph at {m[location_joseph].as_long()}: {m[meet_joseph].as_long()} minutes")
    elif m[meet_sandra].as_long() == 75:
        print(f"Meet Sandra at {m[location_sandra].as_long()}: {m[meet_sandra].as_long()} minutes")
    else:
        print(f"Meet Nancy at {m[location_nancy].as_long()}: {m[meet_nancy].as_long()} minutes")
else:
    print("No solution found")