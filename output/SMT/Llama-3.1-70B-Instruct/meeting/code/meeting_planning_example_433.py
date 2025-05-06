from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
emily_start = 19 * 60  # Convert to minutes
emily_end = 21 * 60  # Convert to minutes
margaret_start = 16 * 60 + 30  # Convert to minutes
margaret_end = 20 * 60 + 15  # Convert to minutes
ronald_start = 18 * 60 + 30  # Convert to minutes
ronald_end = 19 * 60 + 30  # Convert to minutes
deborah_start = 13 * 60 + 45  # Convert to minutes
deborah_end = 21 * 60 + 15  # Convert to minutes
jeffrey_start = 11 * 60 + 15  # Convert to minutes
jeffrey_end = 14 * 60 + 30  # Convert to minutes

travel_time = {
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Golden Gate Park'): 23,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 20,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
}

# Define variables for meeting times
emily_meet = Int('emily_meet')
margaret_meet = Int('margaret_meet')
ronald_meet = Int('ronald_meet')
deborah_meet = Int('deborah_meet')
jeffrey_meet = Int('jeffrey_meet')

# Define variables for travel times
nh_rd = Int('nh_rd')
nh_fd = Int('nh_fd')
nh_nb = Int('nh_nb')
nh_tc = Int('nh_tc')
nh_ggp = Int('nh_ggp')
rd_nh = Int('rd_nh')
rd_fd = Int('rd_fd')
rd_nb = Int('rd_nb')
rd_tc = Int('rd_tc')
rd_ggp = Int('rd_ggp')
fd_nh = Int('fd_nh')
fd_rd = Int('fd_rd')
fd_nb = Int('fd_nb')
fd_tc = Int('fd_tc')
fd_ggp = Int('fd_ggp')
nb_nh = Int('nb_nh')
nb_rd = Int('nb_rd')
nb_fd = Int('nb_fd')
nb_tc = Int('nb_tc')
nb_ggp = Int('nb_ggp')
tc_nh = Int('tc_nh')
tc_rd = Int('tc_rd')
tc_fd = Int('tc_fd')
tc_nb = Int('tc_nb')
tc_ggp = Int('tc_ggp')
ggp_nh = Int('ggp_nh')
ggp_rd = Int('ggp_rd')
ggp_fd = Int('ggp_fd')
ggp_nb = Int('ggp_nb')
ggp_tc = Int('ggp_tc')

# Create solver
s = Solver()

# Add constraints
s.add(emily_meet >= 15)
s.add(margaret_meet >= 75)
s.add(ronald_meet >= 45)
s.add(deborah_meet >= 90)
s.add(jeffrey_meet >= 120)

s.add(emily_meet + nh_rd <= emily_end - emily_start)
s.add(margaret_meet + nh_fd <= margaret_end - margaret_start)
s.add(ronald_meet + nh_nb <= ronald_end - ronald_start)
s.add(deborah_meet + nh_tc <= deborah_end - deborah_start)
s.add(jeffrey_meet + nh_ggp <= jeffrey_end - jeffrey_start)

s.add(nh_rd >= travel_time[('Nob Hill', 'Richmond District')])
s.add(nh_fd >= travel_time[('Nob Hill', 'Financial District')])
s.add(nh_nb >= travel_time[('Nob Hill', 'North Beach')])
s.add(nh_tc >= travel_time[('Nob Hill', 'The Castro')])
s.add(nh_ggp >= travel_time[('Nob Hill', 'Golden Gate Park')])

s.add(rd_nh >= travel_time[('Richmond District', 'Nob Hill')])
s.add(rd_fd >= travel_time[('Richmond District', 'Financial District')])
s.add(rd_nb >= travel_time[('Richmond District', 'North Beach')])
s.add(rd_tc >= travel_time[('Richmond District', 'The Castro')])
s.add(rd_ggp >= travel_time[('Richmond District', 'Golden Gate Park')])

s.add(fd_nh >= travel_time[('Financial District', 'Nob Hill')])
s.add(fd_rd >= travel_time[('Financial District', 'Richmond District')])
s.add(fd_nb >= travel_time[('Financial District', 'North Beach')])
s.add(fd_tc >= travel_time[('Financial District', 'The Castro')])
s.add(fd_ggp >= travel_time[('Financial District', 'Golden Gate Park')])

s.add(nb_nh >= travel_time[('North Beach', 'Nob Hill')])
s.add(nb_rd >= travel_time[('North Beach', 'Richmond District')])
s.add(nb_fd >= travel_time[('North Beach', 'Financial District')])
s.add(nb_tc >= travel_time[('North Beach', 'The Castro')])
s.add(nb_ggp >= travel_time[('North Beach', 'Golden Gate Park')])

s.add(tc_nh >= travel_time[('The Castro', 'Nob Hill')])
s.add(tc_rd >= travel_time[('The Castro', 'Richmond District')])
s.add(tc_fd >= travel_time[('The Castro', 'Financial District')])
s.add(tc_nb >= travel_time[('The Castro', 'North Beach')])
s.add(tc_ggp >= travel_time[('The Castro', 'Golden Gate Park')])

s.add(ggp_nh >= travel_time[('Golden Gate Park', 'Nob Hill')])
s.add(ggp_rd >= travel_time[('Golden Gate Park', 'Richmond District')])
s.add(ggp_fd >= travel_time[('Golden Gate Park', 'Financial District')])
s.add(ggp_nb >= travel_time[('Golden Gate Park', 'North Beach')])
s.add(ggp_tc >= travel_time[('Golden Gate Park', 'The Castro')])

# Optimize
s.maximize(emily_meet + margaret_meet + ronald_meet + deborah_meet + jeffrey_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Emily for", m[emily_meet], "minutes")
    print("Meet Margaret for", m[margaret_meet], "minutes")
    print("Meet Ronald for", m[ronald_meet], "minutes")
    print("Meet Deborah for", m[deborah_meet], "minutes")
    print("Meet Jeffrey for", m[jeffrey_meet], "minutes")
else:
    print("No solution found")