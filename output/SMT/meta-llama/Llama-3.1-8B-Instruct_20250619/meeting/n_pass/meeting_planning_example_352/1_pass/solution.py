from z3 import *

# Define the variables
arrive_union_square = 0
meet_karen = Int('meet_karen')
meet_joseph = Int('meet_joseph')
meet_sandra = Int('meet_sandra')
meet_nancy = Int('meet_nancy')
leave_union_square = arrive_union_square + meet_karen + meet_joseph + meet_sandra + meet_nancy

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
s.add(leave_union_square >= karen_arrive)
s.add(leave_union_square <= karen_leave)
s.add(meet_karen >= 30)

# Joseph
s.add(leave_union_square >= joseph_arrive)
s.add(leave_union_square <= joseph_leave)
s.add(meet_joseph >= 90)

# Sandra
s.add(leave_union_square >= sandra_arrive)
s.add(leave_union_square <= sandra_leave)
s.add(meet_sandra >= 75)

# Nancy
s.add(leave_union_square >= nancy_arrive)
s.add(leave_union_square <= nancy_leave)
s.add(meet_nancy >= 105)

# Travel times
for start, end in travel_times.items():
    if start[0] == 'Union Square':
        s.add(meet_karen + meet_joseph + meet_sandra + meet_nancy >= end)
    else:
        s.add(meet_karen + meet_joseph + meet_sandra + meet_nancy + travel_times[(start[0], 'Union Square')] >= end)

# Solve the problem
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print(f"Meet Karen at Nob Hill: {m[meet_karen].as_long()} minutes")
    print(f"Meet Joseph at Haight-Ashbury: {m[meet_joseph].as_long()} minutes")
    print(f"Meet Sandra at Chinatown: {m[meet_sandra].as_long()} minutes")
    print(f"Meet Nancy at Marina District: {m[meet_nancy].as_long()} minutes")
else:
    print("No solution found")