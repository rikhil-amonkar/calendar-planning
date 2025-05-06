from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
kenneth_start = 12 * 60  # Convert to minutes
kenneth_end = 15 * 60  # Convert to minutes
barbara_start = 8 * 60 + 15  # Convert to minutes
barbara_end = 19 * 60  # Convert to minutes

travel_time = {
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Chinatown'): 23,
}

# Define variables for meeting times
kenneth_meet = Int('kenneth_meet')
barbara_meet = Int('barbara_meet')

# Define variables for travel times
fd_ct = Int('fd_ct')
fd_ggp = Int('fd_ggp')
ct_fd = Int('ct_fd')
ct_ggp = Int('ct_ggp')
ggp_fd = Int('ggp_fd')
ggp_ct = Int('ggp_ct')

# Create solver
s = Solver()

# Add constraints
s.add(kenneth_meet >= 90)
s.add(barbara_meet >= 45)

s.add(kenneth_meet + fd_ct <= kenneth_end - kenneth_start)
s.add(barbara_meet + fd_ggp <= barbara_end - barbara_start)

s.add(fd_ct >= travel_time[('Financial District', 'Chinatown')])
s.add(fd_ggp >= travel_time[('Financial District', 'Golden Gate Park')])
s.add(ct_fd >= travel_time[('Chinatown', 'Financial District')])
s.add(ct_ggp >= travel_time[('Chinatown', 'Golden Gate Park')])
s.add(ggp_fd >= travel_time[('Golden Gate Park', 'Financial District')])
s.add(ggp_ct >= travel_time[('Golden Gate Park', 'Chinatown')])

# Optimize
s.maximize(kenneth_meet + barbara_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Kenneth for", m[kenneth_meet], "minutes")
    print("Meet Barbara for", m[barbara_meet], "minutes")
else:
    print("No solution found")