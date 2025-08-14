from z3 import *

# Define the solver
solver = Solver()

# Define the time variables for each meeting
t_betty_start = Int('t_betty_start')
t_karen_start = Int('t_karen_start')
t_anthony_start = Int('t_anthony_start')

# Define the duration of meetings
betty_duration = 15
karen_duration = 30
anthony_duration = 105

# Define the travel times in minutes
travel_times = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Financial District'): 19,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Financial District'): 5,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Fisherman\'s Wharf'): 10
}

# Define the availability constraints
solver.add(t_karen_start >= 8*60 + 45)  # 8:45 AM
solver.add(t_karen_start + karen_duration <= 15*60)  # 3:00 PM
solver.add(t_anthony_start >= 9*60 + 15)  # 9:15 AM
solver.add(t_anthony_start + anthony_duration <= 21*60 + 45)  # 9:45 PM
solver.add(t_betty_start >= 19*45)  # 7:45 PM
solver.add(t_betty_start + betty_duration <= 21*60 + 45)  # 9:45 PM

# Define the travel constraints
# Start at Bayview at 9:00 AM
start_time = 9*60  # 9:00 AM

# Travel to Karen first (since she has the earliest availability)
solver.add(t_karen_start == start_time + travel_times[('Bayview', 'Fisherman\'s Wharf')])

# Travel from Karen to Anthony
solver.add(t_anthony_start >= t_karen_start + karen_duration + travel_times[('Fisherman\'s Wharf', 'Financial District')])

# Ensure Anthony's meeting fits within his availability
solver.add(t_anthony_start + anthony_duration <= 21*60 + 45)

# Travel from Anthony to Betty
solver.add(t_betty_start >= t_anthony_start + anthony_duration + travel_times[('Financial District', 'Embarcadero')])

# Ensure Betty's meeting fits within her availability
solver.add(t_betty_start + betty_duration <= 21*60 + 45)

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Meet Karen at {model[t_karen_start]} minutes after 9:00 AM")
    print(f"Meet Anthony at {model[t_anthony_start]} minutes after 9:00 AM")
    print(f"Meet Betty at {model[t_betty_start]} minutes after 9:00 AM")
else:
    print("No solution found")

# If the initial solution is not feasible, try a different order
# Start with Anthony, then Karen, then Betty
solver.reset()

# Define the time variables for each meeting
t_betty_start = Int('t_betty_start')
t_karen_start = Int('t_karen_start')
t_anthony_start = Int('t_anthony_start')

# Define the availability constraints
solver.add(t_karen_start >= 8*60 + 45)  # 8:45 AM
solver.add(t_karen_start + karen_duration <= 15*60)  # 3:00 PM
solver.add(t_anthony_start >= 9*60 + 15)  # 9:15 AM
solver.add(t_anthony_start + anthony_duration <= 21*60 + 45)  # 9:45 PM
solver.add(t_betty_start >= 19*45)  # 7:45 PM
solver.add(t_betty_start + betty_duration <= 21*60 + 45)  # 9:45 PM

# Define the travel constraints
# Start at Bayview at 9:00 AM
start_time = 9*60  # 9:00 AM

# Travel to Anthony first
solver.add(t_anthony_start == start_time + travel_times[('Bayview', 'Financial District')])

# Travel from Anthony to Karen
solver.add(t_karen_start >= t_anthony_start + anthony_duration + travel_times[('Financial District', 'Fisherman\'s Wharf')])

# Ensure Karen's meeting fits within her availability
solver.add(t_karen_start + karen_duration <= 15*60)

# Travel from Karen to Betty
solver.add(t_betty_start >= t_karen_start + karen_duration + travel_times[('Fisherman\'s Wharf', 'Embarcadero')])

# Ensure Betty's meeting fits within her availability
solver.add(t_betty_start + betty_duration <= 21*60 + 45)

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Meet Anthony at {model[t_anthony_start]} minutes after 9:00 AM")
    print(f"Meet Karen at {model[t_karen_start]} minutes after 9:00 AM")
    print(f"Meet Betty at {model[t_betty_start]} minutes after 9:00 AM")
else:
    print("No solution found")