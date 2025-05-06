from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
sarah_start = 10 * 60 + 45  # Convert to minutes
sarah_end = 19 * 60  # Convert to minutes
richard_start = 11 * 60 + 45  # Convert to minutes
richard_end = 15 * 60 + 45  # Convert to minutes
elizabeth_start = 11 * 60  # Convert to minutes
elizabeth_end = 17 * 60 + 15  # Convert to minutes
michelle_start = 18 * 60 + 15  # Convert to minutes
michelle_end = 20 * 60 + 45  # Convert to minutes

travel_time = {
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
}

# Define variables for meeting times
sarah_meet = Int('sarah_meet')
richard_meet = Int('richard_meet')
elizabeth_meet = Int('elizabeth_meet')
michelle_meet = Int('michelle_meet')

# Define variables for travel times
rd_sd = Int('rd_sd')
rd_ha = Int('rd_ha')
rd_md = Int('rd_md')
rd_ggp = Int('rd_ggp')
sd_rd = Int('sd_rd')
sd_ha = Int('sd_ha')
sd_md = Int('sd_md')
sd_ggp = Int('sd_ggp')
ha_rd = Int('ha_rd')
ha_sd = Int('ha_sd')
ha_md = Int('ha_md')
ha_ggp = Int('ha_ggp')
md_rd = Int('md_rd')
md_sd = Int('md_sd')
md_ha = Int('md_ha')
md_ggp = Int('md_ggp')
ggp_rd = Int('ggp_rd')
ggp_sd = Int('ggp_sd')
ggp_ha = Int('ggp_ha')
ggp_md = Int('ggp_md')

# Create solver
s = Solver()

# Add constraints
s.add(sarah_meet >= 30)
s.add(richard_meet >= 90)
s.add(elizabeth_meet >= 120)
s.add(michelle_meet >= 90)

s.add(sarah_meet + rd_sd <= sarah_end - sarah_start)
s.add(richard_meet + rd_ha <= richard_end - richard_start)
s.add(elizabeth_meet + rd_md <= elizabeth_end - elizabeth_start)
s.add(michelle_meet + rd_ggp <= michelle_end - michelle_start)

s.add(rd_sd >= travel_time[('Richmond District', 'Sunset District')])
s.add(rd_ha >= travel_time[('Richmond District', 'Haight-Ashbury')])
s.add(rd_md >= travel_time[('Richmond District', 'Mission District')])
s.add(rd_ggp >= travel_time[('Richmond District', 'Golden Gate Park')])

s.add(sd_rd >= travel_time[('Sunset District', 'Richmond District')])
s.add(sd_ha >= travel_time[('Sunset District', 'Haight-Ashbury')])
s.add(sd_md >= travel_time[('Sunset District', 'Mission District')])
s.add(sd_ggp >= travel_time[('Sunset District', 'Golden Gate Park')])

s.add(ha_rd >= travel_time[('Haight-Ashbury', 'Richmond District')])
s.add(ha_sd >= travel_time[('Haight-Ashbury', 'Sunset District')])
s.add(ha_md >= travel_time[('Haight-Ashbury', 'Mission District')])
s.add(ha_ggp >= travel_time[('Haight-Ashbury', 'Golden Gate Park')])

s.add(md_rd >= travel_time[('Mission District', 'Richmond District')])
s.add(md_sd >= travel_time[('Mission District', 'Sunset District')])
s.add(md_ha >= travel_time[('Mission District', 'Haight-Ashbury')])
s.add(md_ggp >= travel_time[('Mission District', 'Golden Gate Park')])

s.add(ggp_rd >= travel_time[('Golden Gate Park', 'Richmond District')])
s.add(ggp_sd >= travel_time[('Golden Gate Park', 'Sunset District')])
s.add(ggp_ha >= travel_time[('Golden Gate Park', 'Haight-Ashbury')])
s.add(ggp_md >= travel_time[('Golden Gate Park', 'Mission District')])

# Optimize
s.maximize(sarah_meet + richard_meet + elizabeth_meet + michelle_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Sarah for", m[sarah_meet], "minutes")
    print("Meet Richard for", m[richard_meet], "minutes")
    print("Meet Elizabeth for", m[elizabeth_meet], "minutes")
    print("Meet Michelle for", m[michelle_meet], "minutes")
else:
    print("No solution found")