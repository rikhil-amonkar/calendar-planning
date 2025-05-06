from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
jason_start = 13 * 60  # Convert to minutes
jason_end = 20 * 60 + 45  # Convert to minutes
melissa_start = 18 * 60 + 45  # Convert to minutes
melissa_end = 20 * 60 + 15  # Convert to minutes
brian_start = 9 * 60 + 45  # Convert to minutes
brian_end = 21 * 60 + 45  # Convert to minutes
elizabeth_start = 8 * 60 + 45  # Convert to minutes
elizabeth_end = 21 * 60 + 30  # Convert to minutes
laura_start = 14 * 60 + 15  # Convert to minutes
laura_end = 19 * 60 + 30  # Convert to minutes

travel_time = {
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Union Square'): 22,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Union Square'): 21,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Union Square'): 7,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Union Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
}

# Define variables for meeting times
jason_meet = Int('jason_meet')
melissa_meet = Int('melissa_meet')
brian_meet = Int('brian_meet')
elizabeth_meet = Int('elizabeth_meet')
laura_meet = Int('laura_meet')

# Define variables for travel times
p_rd = Int('p_rd')
p_nb = Int('p_nb')
p_fd = Int('p_fd')
p_ggp = Int('p_ggp')
p_us = Int('p_us')
rd_p = Int('rd_p')
rd_nb = Int('rd_nb')
rd_fd = Int('rd_fd')
rd_ggp = Int('rd_ggp')
rd_us = Int('rd_us')
nb_p = Int('nb_p')
nb_rd = Int('nb_rd')
nb_fd = Int('nb_fd')
nb_ggp = Int('nb_ggp')
nb_us = Int('nb_us')
fd_p = Int('fd_p')
fd_rd = Int('fd_rd')
fd_nb = Int('fd_nb')
fd_ggp = Int('fd_ggp')
fd_us = Int('fd_us')
ggp_p = Int('ggp_p')
ggp_rd = Int('ggp_rd')
ggp_nb = Int('ggp_nb')
ggp_fd = Int('ggp_fd')
ggp_us = Int('ggp_us')
us_p = Int('us_p')
us_rd = Int('us_rd')
us_nb = Int('us_nb')
us_fd = Int('us_fd')
us_ggp = Int('us_ggp')

# Create solver
s = Solver()

# Add constraints
s.add(jason_meet >= 90)
s.add(melissa_meet >= 45)
s.add(brian_meet >= 15)
s.add(elizabeth_meet >= 105)
s.add(laura_meet >= 75)

s.add(jason_meet + p_rd <= jason_end - jason_start)
s.add(melissa_meet + p_nb <= melissa_end - melissa_start)
s.add(brian_meet + p_fd <= brian_end - brian_start)
s.add(elizabeth_meet + p_ggp <= elizabeth_end - elizabeth_start)
s.add(laura_meet + p_us <= laura_end - laura_start)

s.add(p_rd >= travel_time[('Presidio', 'Richmond District')])
s.add(p_nb >= travel_time[('Presidio', 'North Beach')])
s.add(p_fd >= travel_time[('Presidio', 'Financial District')])
s.add(p_ggp >= travel_time[('Presidio', 'Golden Gate Park')])
s.add(p_us >= travel_time[('Presidio', 'Union Square')])

s.add(rd_p >= travel_time[('Richmond District', 'Presidio')])
s.add(rd_nb >= travel_time[('Richmond District', 'North Beach')])
s.add(rd_fd >= travel_time[('Richmond District', 'Financial District')])
s.add(rd_ggp >= travel_time[('Richmond District', 'Golden Gate Park')])
s.add(rd_us >= travel_time[('Richmond District', 'Union Square')])

s.add(nb_p >= travel_time[('North Beach', 'Presidio')])
s.add(nb_rd >= travel_time[('North Beach', 'Richmond District')])
s.add(nb_fd >= travel_time[('North Beach', 'Financial District')])
s.add(nb_ggp >= travel_time[('North Beach', 'Golden Gate Park')])
s.add(nb_us >= travel_time[('North Beach', 'Union Square')])

s.add(fd_p >= travel_time[('Financial District', 'Presidio')])
s.add(fd_rd >= travel_time[('Financial District', 'Richmond District')])
s.add(fd_nb >= travel_time[('Financial District', 'North Beach')])
s.add(fd_ggp >= travel_time[('Financial District', 'Golden Gate Park')])
s.add(fd_us >= travel_time[('Financial District', 'Union Square')])

s.add(ggp_p >= travel_time[('Golden Gate Park', 'Presidio')])
s.add(ggp_rd >= travel_time[('Golden Gate Park', 'Richmond District')])
s.add(ggp_nb >= travel_time[('Golden Gate Park', 'North Beach')])
s.add(ggp_fd >= travel_time[('Golden Gate Park', 'Financial District')])
s.add(ggp_us >= travel_time[('Golden Gate Park', 'Union Square')])

s.add(us_p >= travel_time[('Union Square', 'Presidio')])
s.add(us_rd >= travel_time[('Union Square', 'Richmond District')])
s.add(us_nb >= travel_time[('Union Square', 'North Beach')])
s.add(us_fd >= travel_time[('Union Square', 'Financial District')])
s.add(us_ggp >= travel_time[('Union Square', 'Golden Gate Park')])

# Optimize
s.maximize(jason_meet + melissa_meet + brian_meet + elizabeth_meet + laura_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Jason for", m[jason_meet], "minutes")
    print("Meet Melissa for", m[melissa_meet], "minutes")
    print("Meet Brian for", m[brian_meet], "minutes")
    print("Meet Elizabeth for", m[elizabeth_meet], "minutes")
    print("Meet Laura for", m[laura_meet], "minutes")
else:
    print("No solution found")