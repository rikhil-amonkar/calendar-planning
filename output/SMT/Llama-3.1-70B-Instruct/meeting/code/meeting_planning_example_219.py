from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
emily_start = 11 * 60 + 45  # Convert to minutes
emily_end = 15 * 60 + 15  # Convert to minutes
barbara_start = 16 * 60 + 45  # Convert to minutes
barbara_end = 18 * 60 + 15  # Convert to minutes
william_start = 17 * 60 + 15  # Convert to minutes
william_end = 19 * 60  # Convert to minutes

travel_time = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7,
}

# Define variables for meeting times
emily_meet = Int('emily_meet')
barbara_meet = Int('barbara_meet')
william_meet = Int('william_meet')

# Define variables for travel times
tc_as = Int('tc_as')
tc_us = Int('tc_us')
tc_ct = Int('tc_ct')
as_tc = Int('as_tc')
as_us = Int('as_us')
as_ct = Int('as_ct')
us_tc = Int('us_tc')
us_as = Int('us_as')
us_ct = Int('us_ct')
ct_tc = Int('ct_tc')
ct_as = Int('ct_as')
ct_us = Int('ct_us')

# Create solver
s = Solver()

# Add constraints
s.add(emily_meet >= 105)
s.add(barbara_meet >= 60)
s.add(william_meet >= 105)

s.add(emily_meet + tc_as <= emily_end - emily_start)
s.add(barbara_meet + tc_us <= barbara_end - barbara_start)
s.add(william_meet + tc_ct <= william_end - william_start)

s.add(tc_as >= travel_time[('The Castro', 'Alamo Square')])
s.add(tc_us >= travel_time[('The Castro', 'Union Square')])
s.add(tc_ct >= travel_time[('The Castro', 'Chinatown')])

s.add(as_tc >= travel_time[('Alamo Square', 'The Castro')])
s.add(as_us >= travel_time[('Alamo Square', 'Union Square')])
s.add(as_ct >= travel_time[('Alamo Square', 'Chinatown')])

s.add(us_tc >= travel_time[('Union Square', 'The Castro')])
s.add(us_as >= travel_time[('Union Square', 'Alamo Square')])
s.add(us_ct >= travel_time[('Union Square', 'Chinatown')])

s.add(ct_tc >= travel_time[('Chinatown', 'The Castro')])
s.add(ct_as >= travel_time[('Chinatown', 'Alamo Square')])
s.add(ct_us >= travel_time[('Chinatown', 'Union Square')])

# Optimize
s.maximize(emily_meet + barbara_meet + william_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Emily for", m[emily_meet], "minutes")
    print("Meet Barbara for", m[barbara_meet], "minutes")
    print("Meet William for", m[william_meet], "minutes")
else:
    print("No solution found")