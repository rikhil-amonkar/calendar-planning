from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
mary_start = 10 * 60  # Convert to minutes
mary_end = 19 * 60  # Convert to minutes
lisa_start = 20 * 60 + 30  # Convert to minutes
lisa_end = 22 * 60  # Convert to minutes
betty_start = 7 * 60 + 15  # Convert to minutes
betty_end = 17 * 60 + 15  # Convert to minutes
charles_start = 11 * 60 + 15  # Convert to minutes
charles_end = 15 * 60  # Convert to minutes

travel_time = {
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Financial District'): 13,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Financial District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Haight-Ashbury'): 19,
}

# Define variables for meeting times
mary_meet = Int('mary_meet')
lisa_meet = Int('lisa_meet')
betty_meet = Int('betty_meet')
charles_meet = Int('charles_meet')

# Define variables for travel times
bv_ph = Int('bv_ph')
bv_md = Int('bv_md')
bv_ha = Int('bv_ha')
bv_fd = Int('bv_fd')
ph_bv = Int('ph_bv')
ph_md = Int('ph_md')
ph_ha = Int('ph_ha')
ph_fd = Int('ph_fd')
md_bv = Int('md_bv')
md_ph = Int('md_ph')
md_ha = Int('md_ha')
md_fd = Int('md_fd')
ha_bv = Int('ha_bv')
ha_ph = Int('ha_ph')
ha_md = Int('ha_md')
ha_fd = Int('ha_fd')
fd_bv = Int('fd_bv')
fd_ph = Int('fd_ph')
fd_md = Int('fd_md')
fd_ha = Int('fd_ha')

# Create solver
s = Solver()

# Add constraints
s.add(mary_meet >= 45)
s.add(lisa_meet >= 75)
s.add(betty_meet >= 90)
s.add(charles_meet >= 120)

s.add(mary_meet + bv_ph <= mary_end - mary_start)
s.add(lisa_meet + bv_md <= lisa_end - lisa_start)
s.add(betty_meet + bv_ha <= betty_end - betty_start)
s.add(charles_meet + bv_fd <= charles_end - charles_start)

s.add(bv_ph >= travel_time[('Bayview', 'Pacific Heights')])
s.add(bv_md >= travel_time[('Bayview', 'Mission District')])
s.add(bv_ha >= travel_time[('Bayview', 'Haight-Ashbury')])
s.add(bv_fd >= travel_time[('Bayview', 'Financial District')])

s.add(ph_bv >= travel_time[('Pacific Heights', 'Bayview')])
s.add(ph_md >= travel_time[('Pacific Heights', 'Mission District')])
s.add(ph_ha >= travel_time[('Pacific Heights', 'Haight-Ashbury')])
s.add(ph_fd >= travel_time[('Pacific Heights', 'Financial District')])

s.add(md_bv >= travel_time[('Mission District', 'Bayview')])
s.add(md_ph >= travel_time[('Mission District', 'Pacific Heights')])
s.add(md_ha >= travel_time[('Mission District', 'Haight-Ashbury')])
s.add(md_fd >= travel_time[('Mission District', 'Financial District')])

s.add(ha_bv >= travel_time[('Haight-Ashbury', 'Bayview')])
s.add(ha_ph >= travel_time[('Haight-Ashbury', 'Pacific Heights')])
s.add(ha_md >= travel_time[('Haight-Ashbury', 'Mission District')])
s.add(ha_fd >= travel_time[('Haight-Ashbury', 'Financial District')])

s.add(fd_bv >= travel_time[('Financial District', 'Bayview')])
s.add(fd_ph >= travel_time[('Financial District', 'Pacific Heights')])
s.add(fd_md >= travel_time[('Financial District', 'Mission District')])
s.add(fd_ha >= travel_time[('Financial District', 'Haight-Ashbury')])

# Optimize
s.maximize(mary_meet + lisa_meet + betty_meet + charles_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Mary for", m[mary_meet], "minutes")
    print("Meet Lisa for", m[lisa_meet], "minutes")
    print("Meet Betty for", m[betty_meet], "minutes")
    print("Meet Charles for", m[charles_meet], "minutes")
else:
    print("No solution found")