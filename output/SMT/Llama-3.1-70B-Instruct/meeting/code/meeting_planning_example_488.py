from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
ronald_start = 10 * 60  # Convert to minutes
ronald_end = 17 * 60  # Convert to minutes
sarah_start = 7 * 60 + 15  # Convert to minutes
sarah_end = 9 * 60 + 30  # Convert to minutes
helen_start = 13 * 60 + 30  # Convert to minutes
helen_end = 17 * 60  # Convert to minutes
joshua_start = 14 * 60 + 15  # Convert to minutes
joshua_end = 19 * 60 + 30  # Convert to minutes
margaret_start = 10 * 60 + 15  # Convert to minutes
margaret_end = 22 * 60  # Convert to minutes

travel_time = {
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 25,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Sunset District'): 15,
}

# Define variables for meeting times
ronald_meet = Int('ronald_meet')
sarah_meet = Int('sarah_meet')
helen_meet = Int('helen_meet')
joshua_meet = Int('joshua_meet')
margaret_meet = Int('margaret_meet')

# Define variables for travel times
ph_nh = Int('ph_nh')
ph_rh = Int('ph_rh')
ph_tc = Int('ph_tc')
ph_sd = Int('ph_sd')
ph_ha = Int('ph_ha')
nh_ph = Int('nh_ph')
nh_rh = Int('nh_rh')
nh_tc = Int('nh_tc')
nh_sd = Int('nh_sd')
nh_ha = Int('nh_ha')
rh_ph = Int('rh_ph')
rh_nh = Int('rh_nh')
rh_tc = Int('rh_tc')
rh_sd = Int('rh_sd')
rh_ha = Int('rh_ha')
tc_ph = Int('tc_ph')
tc_nh = Int('tc_nh')
tc_rh = Int('tc_rh')
tc_sd = Int('tc_sd')
tc_ha = Int('tc_ha')
sd_ph = Int('sd_ph')
sd_nh = Int('sd_nh')
sd_rh = Int('sd_rh')
sd_tc = Int('sd_tc')
sd_ha = Int('sd_ha')
ha_ph = Int('ha_ph')
ha_nh = Int('ha_nh')
ha_rh = Int('ha_rh')
ha_tc = Int('ha_tc')
ha_sd = Int('ha_sd')

# Create solver
s = Solver()

# Add constraints
s.add(ronald_meet >= 105)
s.add(sarah_meet >= 45)
s.add(helen_meet >= 120)
s.add(joshua_meet >= 90)
s.add(margaret_meet >= 60)

s.add(ronald_meet + ph_nh <= ronald_end - ronald_start)
s.add(sarah_meet + ph_rh <= sarah_end - sarah_start)
s.add(helen_meet + ph_tc <= helen_end - helen_start)
s.add(joshua_meet + ph_sd <= joshua_end - joshua_start)
s.add(margaret_meet + ph_ha <= margaret_end - margaret_start)

s.add(ph_nh >= travel_time[('Pacific Heights', 'Nob Hill')])
s.add(ph_rh >= travel_time[('Pacific Heights', 'Russian Hill')])
s.add(ph_tc >= travel_time[('Pacific Heights', 'The Castro')])
s.add(ph_sd >= travel_time[('Pacific Heights', 'Sunset District')])
s.add(ph_ha >= travel_time[('Pacific Heights', 'Haight-Ashbury')])

s.add(nh_ph >= travel_time[('Nob Hill', 'Pacific Heights')])
s.add(nh_rh >= travel_time[('Nob Hill', 'Russian Hill')])
s.add(nh_tc >= travel_time[('Nob Hill', 'The Castro')])
s.add(nh_sd >= travel_time[('Nob Hill', 'Sunset District')])
s.add(nh_ha >= travel_time[('Nob Hill', 'Haight-Ashbury')])

s.add(rh_ph >= travel_time[('Russian Hill', 'Pacific Heights')])
s.add(rh_nh >= travel_time[('Russian Hill', 'Nob Hill')])
s.add(rh_tc >= travel_time[('Russian Hill', 'The Castro')])
s.add(rh_sd >= travel_time[('Russian Hill', 'Sunset District')])
s.add(rh_ha >= travel_time[('Russian Hill', 'Haight-Ashbury')])

s.add(tc_ph >= travel_time[('The Castro', 'Pacific Heights')])
s.add(tc_nh >= travel_time[('The Castro', 'Nob Hill')])
s.add(tc_rh >= travel_time[('The Castro', 'Russian Hill')])
s.add(tc_sd >= travel_time[('The Castro', 'Sunset District')])
s.add(tc_ha >= travel_time[('The Castro', 'Haight-Ashbury')])

s.add(sd_ph >= travel_time[('Sunset District', 'Pacific Heights')])
s.add(sd_nh >= travel_time[('Sunset District', 'Nob Hill')])
s.add(sd_rh >= travel_time[('Sunset District', 'Russian Hill')])
s.add(sd_tc >= travel_time[('Sunset District', 'The Castro')])
s.add(sd_ha >= travel_time[('Sunset District', 'Haight-Ashbury')])

s.add(ha_ph >= travel_time[('Haight-Ashbury', 'Pacific Heights')])
s.add(ha_nh >= travel_time[('Haight-Ashbury', 'Nob Hill')])
s.add(ha_rh >= travel_time[('Haight-Ashbury', 'Russian Hill')])
s.add(ha_tc >= travel_time[('Haight-Ashbury', 'The Castro')])
s.add(ha_sd >= travel_time[('Haight-Ashbury', 'Sunset District')])

# Optimize
s.maximize(ronald_meet + sarah_meet + helen_meet + joshua_meet + margaret_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Ronald for", m[ronald_meet], "minutes")
    print("Meet Sarah for", m[sarah_meet], "minutes")
    print("Meet Helen for", m[helen_meet], "minutes")
    print("Meet Joshua for", m[joshua_meet], "minutes")
    print("Meet Margaret for", m[margaret_meet], "minutes")
else:
    print("No solution found")