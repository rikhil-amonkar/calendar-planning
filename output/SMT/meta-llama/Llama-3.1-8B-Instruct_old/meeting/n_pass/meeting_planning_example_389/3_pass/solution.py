from z3 import *

# Define the travel distances
distances = {
    'HA': {'FA': 23, 'RD': 10, 'MD': 11, 'BV': 18},
    'FA': {'HA': 22, 'RD': 18, 'MD': 22, 'BV': 26},
    'RD': {'HA': 10, 'FA': 18, 'MD': 20, 'BV': 26},
    'MD': {'HA': 11, 'FA': 22, 'RD': 20, 'BV': 15},
    'BV': {'HA': 18, 'FA': 25, 'RD': 25, 'MD': 13}
}

# Define the constraints
s = Solver()

# Define the variables
t_ha = Int('t_ha')
t_fa = Int('t_fa')
t_rd = Int('t_rd')
t_md = Int('t_md')
t_bv = Int('t_bv')

# Sarah's availability
s_add = s.add(And(2*45 + 105 <= t_fa, t_fa <= 5*30))
s_add = s.add(t_fa >= 9*60 + 1)  # Ensure we visit Sarah at least 1 minute after 9:00 AM
s_add = s.add(t_fa >= t_ha + distances['HA']['FA'])

# Mary's availability
m_add = s.add(And(1*60 + 75 <= t_rd, t_rd <= 7*15))
m_add = s.add(t_rd >= t_ha + distances['HA']['RD'])

# Thomas' availability
th_add = s.add(And(3*15 + 120 <= t_bv, t_bv <= 6*45))
th_add = s.add(t_bv >= t_ha + distances['HA']['BV'])

# Total time constraint
s_add = s.add(t_ha + t_fa + t_rd + t_bv >= 9*60)

# Solve the problem
s.check()
m = s.model()

# Print the solution
print("SOLUTION:")
print(f"Travel to Fisherman's Wharf: {m[t_fa] - m[t_ha]} minutes")
print(f"Travel to Richmond District: {m[t_rd] - m[t_ha]} minutes")
print(f"Travel to Bayview: {m[t_bv] - m[t_ha]} minutes")
print(f"Total time: {m[t_ha] + m[t_fa] + m[t_rd] + m[t_bv]} minutes")