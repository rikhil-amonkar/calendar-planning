from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
sarah_start = 14 * 60 + 45  # Convert to minutes
sarah_end = 17 * 60 + 30  # Convert to minutes
mary_start = 13 * 60  # Convert to minutes
mary_end = 19 * 60 + 15  # Convert to minutes
helen_start = 21 * 60 + 45  # Convert to minutes
helen_end = 22 * 60 + 30  # Convert to minutes
thomas_start = 15 * 60 + 15  # Convert to minutes
thomas_end = 18 * 60 + 45  # Convert to minutes

travel_time = {
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Bayview'): 26,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Bayview'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Mission District'): 13,
}

# Define variables for meeting times
sarah_meet = Int('sarah_meet')
mary_meet = Int('mary_meet')
helen_meet = Int('helen_meet')
thomas_meet = Int('thomas_meet')

# Define variables for travel times
ha_fw = Int('ha_fw')
ha_rd = Int('ha_rd')
ha_md = Int('ha_md')
ha_bv = Int('ha_bv')
fw_ha = Int('fw_ha')
fw_rd = Int('fw_rd')
fw_md = Int('fw_md')
fw_bv = Int('fw_bv')
rd_ha = Int('rd_ha')
rd_fw = Int('rd_fw')
rd_md = Int('rd_md')
rd_bv = Int('rd_bv')
md_ha = Int('md_ha')
md_fw = Int('md_fw')
md_rd = Int('md_rd')
md_bv = Int('md_bv')
bv_ha = Int('bv_ha')
bv_fw = Int('bv_fw')
bv_rd = Int('bv_rd')
bv_md = Int('bv_md')

# Create solver
s = Solver()

# Add constraints
s.add(sarah_meet >= 105)
s.add(mary_meet >= 75)
s.add(helen_meet >= 30)
s.add(thomas_meet >= 120)

s.add(sarah_meet + ha_fw <= sarah_end - sarah_start)
s.add(mary_meet + ha_rd <= mary_end - mary_start)
s.add(helen_meet + ha_md <= helen_end - helen_start)
s.add(thomas_meet + ha_bv <= thomas_end - thomas_start)

s.add(ha_fw >= travel_time[('Haight-Ashbury', 'Fisherman\'s Wharf')])
s.add(ha_rd >= travel_time[('Haight-Ashbury', 'Richmond District')])
s.add(ha_md >= travel_time[('Haight-Ashbury', 'Mission District')])
s.add(ha_bv >= travel_time[('Haight-Ashbury', 'Bayview')])

s.add(fw_ha >= travel_time[('Fisherman\'s Wharf', 'Haight-Ashbury')])
s.add(fw_rd >= travel_time[('Fisherman\'s Wharf', 'Richmond District')])
s.add(fw_md >= travel_time[('Fisherman\'s Wharf', 'Mission District')])
s.add(fw_bv >= travel_time[('Fisherman\'s Wharf', 'Bayview')])

s.add(rd_ha >= travel_time[('Richmond District', 'Haight-Ashbury')])
s.add(rd_fw >= travel_time[('Richmond District', 'Fisherman\'s Wharf')])
s.add(rd_md >= travel_time[('Richmond District', 'Mission District')])
s.add(rd_bv >= travel_time[('Richmond District', 'Bayview')])

s.add(md_ha >= travel_time[('Mission District', 'Haight-Ashbury')])
s.add(md_fw >= travel_time[('Mission District', 'Fisherman\'s Wharf')])
s.add(md_rd >= travel_time[('Mission District', 'Richmond District')])
s.add(md_bv >= travel_time[('Mission District', 'Bayview')])

s.add(bv_ha >= travel_time[('Bayview', 'Haight-Ashbury')])
s.add(bv_fw >= travel_time[('Bayview', 'Fisherman\'s Wharf')])
s.add(bv_rd >= travel_time[('Bayview', 'Richmond District')])
s.add(bv_md >= travel_time[('Bayview', 'Mission District')])

# Optimize
s.maximize(sarah_meet + mary_meet + helen_meet + thomas_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Sarah for", m[sarah_meet], "minutes")
    print("Meet Mary for", m[mary_meet], "minutes")
    print("Meet Helen for", m[helen_meet], "minutes")
    print("Meet Thomas for", m[thomas_meet], "minutes")
else:
    print("No solution found")