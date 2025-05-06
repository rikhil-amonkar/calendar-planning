from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
betty_start = 10 * 60 + 15  # Convert to minutes
betty_end = 21 * 60 + 30  # Convert to minutes
david_start = 13 * 60  # Convert to minutes
david_end = 20 * 60 + 15  # Convert to minutes
barbara_start = 9 * 60 + 15  # Convert to minutes
barbara_end = 20 * 60 + 15  # Convert to minutes

travel_time = {
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

# Define variables for meeting times
betty_meet = Int('betty_meet')
david_meet = Int('david_meet')
barbara_meet = Int('barbara_meet')

# Define variables for travel times
em_pr = Int('em_pr')
em_rd = Int('em_rd')
em_fw = Int('em_fw')
pr_em = Int('pr_em')
pr_rd = Int('pr_rd')
pr_fw = Int('pr_fw')
rd_em = Int('rd_em')
rd_pr = Int('rd_pr')
rd_fw = Int('rd_fw')
fw_em = Int('fw_em')
fw_pr = Int('fw_pr')
fw_rd = Int('fw_rd')

# Create solver
s = Solver()

# Add constraints
s.add(betty_meet >= 45)
s.add(david_meet >= 90)
s.add(barbara_meet >= 120)

s.add(betty_meet + em_pr <= betty_end - betty_start)
s.add(david_meet + em_rd <= david_end - david_start)
s.add(barbara_meet + em_fw <= barbara_end - barbara_start)

s.add(em_pr >= travel_time[('Embarcadero', 'Presidio')])
s.add(em_rd >= travel_time[('Embarcadero', 'Richmond District')])
s.add(em_fw >= travel_time[('Embarcadero', 'Fisherman\'s Wharf')])

s.add(pr_em >= travel_time[('Presidio', 'Embarcadero')])
s.add(pr_rd >= travel_time[('Presidio', 'Richmond District')])
s.add(pr_fw >= travel_time[('Presidio', 'Fisherman\'s Wharf')])

s.add(rd_em >= travel_time[('Richmond District', 'Embarcadero')])
s.add(rd_pr >= travel_time[('Richmond District', 'Presidio')])
s.add(rd_fw >= travel_time[('Richmond District', 'Fisherman\'s Wharf')])

s.add(fw_em >= travel_time[('Fisherman\'s Wharf', 'Embarcadero')])
s.add(fw_pr >= travel_time[('Fisherman\'s Wharf', 'Presidio')])
s.add(fw_rd >= travel_time[('Fisherman\'s Wharf', 'Richmond District')])

# Optimize
s.maximize(betty_meet + david_meet + barbara_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Betty for", m[betty_meet], "minutes")
    print("Meet David for", m[david_meet], "minutes")
    print("Meet Barbara for", m[barbara_meet], "minutes")
else:
    print("No solution found")