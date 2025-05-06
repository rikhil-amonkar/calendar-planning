from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
david_start = 10 * 60 + 45  # Convert to minutes
david_end = 15 * 60 + 30  # Convert to minutes
timothy_start = 9 * 60  # Convert to minutes
timothy_end = 15 * 60 + 30  # Convert to minutes
robert_start = 12 * 60 + 15  # Convert to minutes
robert_end = 19 * 60 + 45  # Convert to minutes

travel_time = {
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Pacific Heights'): 16,
}

# Define variables for meeting times
david_meet = Int('david_meet')
timothy_meet = Int('timothy_meet')
robert_meet = Int('robert_meet')

# Define variables for travel times
fd_fw = Int('fd_fw')
fd_ph = Int('fd_ph')
fd_md = Int('fd_md')
fw_fd = Int('fw_fd')
fw_ph = Int('fw_ph')
fw_md = Int('fw_md')
ph_fd = Int('ph_fd')
ph_fw = Int('ph_fw')
ph_md = Int('ph_md')
md_fd = Int('md_fd')
md_fw = Int('md_fw')
md_ph = Int('md_ph')

# Create solver
s = Solver()

# Add constraints
s.add(david_meet >= 15)
s.add(timothy_meet >= 75)
s.add(robert_meet >= 90)

s.add(david_meet + fd_fw <= david_end - david_start)
s.add(timothy_meet + fd_ph <= timothy_end - timothy_start)
s.add(robert_meet + fd_md <= robert_end - robert_start)

s.add(fd_fw >= travel_time[('Financial District', 'Fisherman\'s Wharf')])
s.add(fd_ph >= travel_time[('Financial District', 'Pacific Heights')])
s.add(fd_md >= travel_time[('Financial District', 'Mission District')])

s.add(fw_fd >= travel_time[('Fisherman\'s Wharf', 'Financial District')])
s.add(fw_ph >= travel_time[('Fisherman\'s Wharf', 'Pacific Heights')])
s.add(fw_md >= travel_time[('Fisherman\'s Wharf', 'Mission District')])

s.add(ph_fd >= travel_time[('Pacific Heights', 'Financial District')])
s.add(ph_fw >= travel_time[('Pacific Heights', 'Fisherman\'s Wharf')])
s.add(ph_md >= travel_time[('Pacific Heights', 'Mission District')])

s.add(md_fd >= travel_time[('Mission District', 'Financial District')])
s.add(md_fw >= travel_time[('Mission District', 'Fisherman\'s Wharf')])
s.add(md_ph >= travel_time[('Mission District', 'Pacific Heights')])

# Optimize
s.maximize(david_meet + timothy_meet + robert_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet David for", m[david_meet], "minutes")
    print("Meet Timothy for", m[timothy_meet], "minutes")
    print("Meet Robert for", m[robert_meet], "minutes")
else:
    print("No solution found")