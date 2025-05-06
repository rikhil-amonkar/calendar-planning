from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
emily_start = 16 * 60  # Convert to minutes
emily_end = 17 * 60 + 15  # Convert to minutes
margaret_start = 19 * 60  # Convert to minutes
margaret_end = 21 * 60  # Convert to minutes

travel_time = {
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Russian Hill'): 4,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Russian Hill'): 13,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Union Square'): 11,
}

# Define variables for meeting times
emily_meet = Int('emily_meet')
margaret_meet = Int('margaret_meet')

# Define variables for travel times
nb_us = Int('nb_us')
nb_rh = Int('nb_rh')
us_nb = Int('us_nb')
us_rh = Int('us_rh')
rh_nb = Int('rh_nb')
rh_us = Int('rh_us')

# Create solver
s = Solver()

# Add constraints
s.add(emily_meet >= 45)
s.add(margaret_meet >= 120)

s.add(emily_meet + nb_us <= emily_end - emily_start)
s.add(margaret_meet + nb_rh <= margaret_end - margaret_start)

s.add(nb_us >= travel_time[('North Beach', 'Union Square')])
s.add(nb_rh >= travel_time[('North Beach', 'Russian Hill')])

s.add(us_nb >= travel_time[('Union Square', 'North Beach')])
s.add(us_rh >= travel_time[('Union Square', 'Russian Hill')])

s.add(rh_nb >= travel_time[('Russian Hill', 'North Beach')])
s.add(rh_us >= travel_time[('Russian Hill', 'Union Square')])

# Optimize
s.maximize(emily_meet + margaret_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Emily for", m[emily_meet], "minutes")
    print("Meet Margaret for", m[margaret_meet], "minutes")
else:
    print("No solution found")