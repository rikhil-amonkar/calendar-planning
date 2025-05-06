from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
kevin_start = 7 * 60 + 15  # Convert to minutes
kevin_end = 8 * 60 + 45  # Convert to minutes
michelle_start = 20 * 60  # Convert to minutes
michelle_end = 21 * 60  # Convert to minutes
emily_start = 16 * 60 + 15  # Convert to minutes
emily_end = 19 * 60  # Convert to minutes
mark_start = 18 * 60 + 15  # Convert to minutes
mark_end = 19 * 60 + 45  # Convert to minutes
barbara_start = 17 * 60  # Convert to minutes
barbara_end = 19 * 60  # Convert to minutes
laura_start = 19 * 60  # Convert to minutes
laura_end = 21 * 60 + 15  # Convert to minutes
mary_start = 17 * 60 + 30  # Convert to minutes
mary_end = 19 * 60  # Convert to minutes
helen_start = 11 * 60  # Convert to minutes
helen_end = 12 * 60 + 15  # Convert to minutes

travel_time = {
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'North Beach'): 18,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'North Beach'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'North Beach'): 11,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'North Beach'): 15,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'North Beach'): 28,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'North Beach'): 8,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Nob Hill'): 7,
}

# Define variables for meeting times
kevin_meet = Int('kevin_meet')
michelle_meet = Int('michelle_meet')
emily_meet = Int('emily_meet')
mark_meet = Int('mark_meet')
barbara_meet = Int('barbara_meet')
laura_meet = Int('laura_meet')
mary_meet = Int('mary_meet')
helen_meet = Int('helen_meet')

# Define variables for travel times
p_ph = Int('p_ph')
p_ggp = Int('p_ggp')
p_fw = Int('p_fw')
p_md = Int('p_md')
p_as = Int('p_as')
p_sd = Int('p_sd')
p_nh = Int('p_nh')
p_nb = Int('p_nb')
ph_p = Int('ph_p')
ph_ggp = Int('ph_ggp')
ph_fw = Int('ph_fw')
ph_md = Int('ph_md')
ph_as = Int('ph_as')
ph_sd = Int('ph_sd')
ph_nh = Int('ph_nh')
ph_nb = Int('ph_nb')
ggp_p = Int('ggp_p')
ggp_ph = Int('ggp_ph')
ggp_fw = Int('ggp_fw')
ggp_md = Int('ggp_md')
ggp_as = Int('ggp_as')
ggp_sd = Int('ggp_sd')
ggp_nh = Int('ggp_nh')
ggp_nb = Int('ggp_nb')
fw_p = Int('fw_p')
fw_ph = Int('fw_ph')
fw_ggp = Int('fw_ggp')
fw_md = Int('fw_md')
fw_as = Int('fw_as')
fw_sd = Int('fw_sd')
fw_nh = Int('fw_nh')
fw_nb = Int('fw_nb')
md_p = Int('md_p')
md_ph = Int('md_ph')
md_ggp = Int('md_ggp')
md_fw = Int('md_fw')
md_as = Int('md_as')
md_sd = Int('md_sd')
md_nh = Int('md_nh')
md_nb = Int('md_nb')
as_p = Int('as_p')
as_ph = Int('as_ph')
as_ggp = Int('as_ggp')
as_fw = Int('as_fw')
as_md = Int('as_md')
as_sd = Int('as_sd')
as_nh = Int('as_nh')
as_nb = Int('as_nb')
sd_p = Int('sd_p')
sd_ph = Int('sd_ph')
sd_ggp = Int('sd_ggp')
sd_fw = Int('sd_fw')
sd_md = Int('sd_md')
sd_as = Int('sd_as')
sd_nh = Int('sd_nh')
sd_nb = Int('sd_nb')
nh_p = Int('nh_p')
nh_ph = Int('nh_ph')
nh_ggp = Int('nh_ggp')
nh_fw = Int('nh_fw')
nh_md = Int('nh_md')
nh_as = Int('nh_as')
nh_sd = Int('nh_sd')
nh_nb = Int('nh_nb')
nb_p = Int('nb_p')
nb_ph = Int('nb_ph')
nb_ggp = Int('nb_ggp')
nb_fw = Int('nb_fw')
nb_md = Int('nb_md')
nb_as = Int('nb_as')
nb_sd = Int('nb_sd')
nb_nh = Int('nb_nh')

# Create solver
s = Solver()

# Add constraints
s.add(kevin_meet >= 90)
s.add(michelle_meet >= 15)
s.add(emily_meet >= 30)
s.add(mark_meet >= 75)
s.add(barbara_meet >= 120)
s.add(laura_meet >= 75)
s.add(mary_meet >= 45)
s.add(helen_meet >= 45)

s.add(kevin_meet + p_ph <= kevin_end - kevin_start)
s.add(michelle_meet + p_ggp <= michelle_end - michelle_start)
s.add(emily_meet + p_fw <= emily_end - emily_start)
s.add(mark_meet + p_md <= mark_end - mark_start)
s.add(barbara_meet + p_as <= barbara_end - barbara_start)
s.add(laura_meet + p_sd <= laura_end - laura_start)
s.add(mary_meet + p_nh <= mary_end - mary_start)
s.add(helen_meet + p_nb <= helen_end - helen_start)

s.add(p_ph >= travel_time[('Presidio', 'Pacific Heights')])
s.add(p_ggp >= travel_time[('Presidio', 'Golden Gate Park')])
s.add(p_fw >= travel_time[('Presidio', 'Fisherman\'s Wharf')])
s.add(p_md >= travel_time[('Presidio', 'Marina District')])
s.add(p_as >= travel_time[('Presidio', 'Alamo Square')])
s.add(p_sd >= travel_time[('Presidio', 'Sunset District')])
s.add(p_nh >= travel_time[('Presidio', 'Nob Hill')])
s.add(p_nb >= travel_time[('Presidio', 'North Beach')])

s.add(ph_p >= travel_time[('Pacific Heights', 'Presidio')])
s.add(ph_ggp >= travel_time[('Pacific Heights', 'Golden Gate Park')])
s.add(ph_fw >= travel_time[('Pacific Heights', 'Fisherman\'s Wharf')])
s.add(ph_md >= travel_time[('Pacific Heights', 'Marina District')])
s.add(ph_as >= travel_time[('Pacific Heights', 'Alamo Square')])
s.add(ph_sd >= travel_time[('Pacific Heights', 'Sunset District')])
s.add(ph_nh >= travel_time[('Pacific Heights', 'Nob Hill')])
s.add(ph_nb >= travel_time[('Pacific Heights', 'North Beach')])

s.add(ggp_p >= travel_time[('Golden Gate Park', 'Presidio')])
s.add(ggp_ph >= travel_time[('Golden Gate Park', 'Pacific Heights')])
s.add(ggp_fw >= travel_time[('Golden Gate Park', 'Fisherman\'s Wharf')])
s.add(ggp_md >= travel_time[('Golden Gate Park', 'Marina District')])
s.add(ggp_as >= travel_time[('Golden Gate Park', 'Alamo Square')])
s.add(ggp_sd >= travel_time[('Golden Gate Park', 'Sunset District')])
s.add(ggp_nh >= travel_time[('Golden Gate Park', 'Nob Hill')])
s.add(ggp_nb >= travel_time[('Golden Gate Park', 'North Beach')])

s.add(fw_p >= travel_time[('Fisherman\'s Wharf', 'Presidio')])
s.add(fw_ph >= travel_time[('Fisherman\'s Wharf', 'Pacific Heights')])
s.add(fw_ggp >= travel_time[('Fisherman\'s Wharf', 'Golden Gate Park')])
s.add(fw_md >= travel_time[('Fisherman\'s Wharf', 'Marina District')])
s.add(fw_as >= travel_time[('Fisherman\'s Wharf', 'Alamo Square')])
s.add(fw_sd >= travel_time[('Fisherman\'s Wharf', 'Sunset District')])
s.add(fw_nh >= travel_time[('Fisherman\'s Wharf', 'Nob Hill')])
s.add(fw_nb >= travel_time[('Fisherman\'s Wharf', 'North Beach')])

s.add(md_p >= travel_time[('Marina District', 'Presidio')])
s.add(md_ph >= travel_time[('Marina District', 'Pacific Heights')])
s.add(md_ggp >= travel_time[('Marina District', 'Golden Gate Park')])
s.add(md_fw >= travel_time[('Marina District', 'Fisherman\'s Wharf')])
s.add(md_as >= travel_time[('Marina District', 'Alamo Square')])
s.add(md_sd >= travel_time[('Marina District', 'Sunset District')])
s.add(md_nh >= travel_time[('Marina District', 'Nob Hill')])
s.add(md_nb >= travel_time[('Marina District', 'North Beach')])

s.add(as_p >= travel_time[('Alamo Square', 'Presidio')])
s.add(as_ph >= travel_time[('Alamo Square', 'Pacific Heights')])
s.add(as_ggp >= travel_time[('Alamo Square', 'Golden Gate Park')])
s.add(as_fw >= travel_time[('Alamo Square', 'Fisherman\'s Wharf')])
s.add(as_md >= travel_time[('Alamo Square', 'Marina District')])
s.add(as_sd >= travel_time[('Alamo Square', 'Sunset District')])
s.add(as_nh >= travel_time[('Alamo Square', 'Nob Hill')])
s.add(as_nb >= travel_time[('Alamo Square', 'North Beach')])

s.add(sd_p >= travel_time[('Sunset District', 'Presidio')])
s.add(sd_ph >= travel_time[('Sunset District', 'Pacific Heights')])
s.add(sd_ggp >= travel_time[('Sunset District', 'Golden Gate Park')])
s.add(sd_fw >= travel_time[('Sunset District', 'Fisherman\'s Wharf')])
s.add(sd_md >= travel_time[('Sunset District', 'Marina District')])
s.add(sd_as >= travel_time[('Sunset District', 'Alamo Square')])
s.add(sd_nh >= travel_time[('Sunset District', 'Nob Hill')])
s.add(sd_nb >= travel_time[('Sunset District', 'North Beach')])

s.add(nh_p >= travel_time[('Nob Hill', 'Presidio')])
s.add(nh_ph >= travel_time[('Nob Hill', 'Pacific Heights')])
s.add(nh_ggp >= travel_time[('Nob Hill', 'Golden Gate Park')])
s.add(nh_fw >= travel_time[('Nob Hill', 'Fisherman\'s Wharf')])
s.add(nh_md >= travel_time[('Nob Hill', 'Marina District')])
s.add(nh_as >= travel_time[('Nob Hill', 'Alamo Square')])
s.add(nh_sd >= travel_time[('Nob Hill', 'Sunset District')])
s.add(nh_nb >= travel_time[('Nob Hill', 'North Beach')])

s.add(nb_p >= travel_time[('North Beach', 'Presidio')])
s.add(nb_ph >= travel_time[('North Beach', 'Pacific Heights')])
s.add(nb_ggp >= travel_time[('North Beach', 'Golden Gate Park')])
s.add(nb_fw >= travel_time[('North Beach', 'Fisherman\'s Wharf')])
s.add(nb_md >= travel_time[('North Beach', 'Marina District')])
s.add(nb_as >= travel_time[('North Beach', 'Alamo Square')])
s.add(nb_sd >= travel_time[('North Beach', 'Sunset District')])
s.add(nb_nh >= travel_time[('North Beach', 'Nob Hill')])

# Optimize
s.maximize(kevin_meet + michelle_meet + emily_meet + mark_meet + barbara_meet + laura_meet + mary_meet + helen_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Kevin for", m[kevin_meet], "minutes")
    print("Meet Michelle for", m[michelle_meet], "minutes")
    print("Meet Emily for", m[emily_meet], "minutes")
    print("Meet Mark for", m[mark_meet], "minutes")
    print("Meet Barbara for", m[barbara_meet], "minutes")
    print("Meet Laura for", m[laura_meet], "minutes")
    print("Meet Mary for", m[mary_meet], "minutes")
    print("Meet Helen for", m[helen_meet], "minutes")
else:
    print("No solution found")