from z3 import *

# Create a solver instance
solver = Solver()

# Define time variables for meeting Stephanie and John
t_start_stephanie = Int('t_start_stephanie')
t_end_stephanie = Int('t_end_stephanie')
t_start_john = Int('t_start_john')
t_end_john = Int('t_end_john')

# Define the arrival time at Embarcadero
arrival_time = 9 * 60  # 9:00 AM in minutes

# Constraints for meeting Stephanie
solver.add(t_start_stephanie >= 8 * 60 + 15)  # Stephanie is available from 8:15 AM
solver.add(t_end_stephanie <= 11 * 60 + 30)   # Stephanie is available until 11:30 AM
solver.add(t_end_stephanie - t_start_stephanie >= 90)  # Minimum 90 minutes with Stephanie

# Constraints for meeting John
solver.add(t_start_john >= 10 * 60 + 15)  # John is available from 10:15 AM
solver.add(t_end_john <= 20 * 60 + 45)    # John is available until 8:45 PM
solver.add(t_end_john - t_start_john >= 30)  # Minimum 30 minutes with John

# Travel times in minutes
travel_times = {
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Alamo Square'): 17,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Financial District'): 17
}

# Ensure you can travel between locations within the time constraints
# Assume you start at Embarcadero at 9:00 AM
# If you meet Stephanie first, then John
solver.add(t_start_stephanie >= arrival_time + travel_times[('Embarcadero', 'Financial District')])
solver.add(t_start_john >= t_end_stephanie + travel_times[('Financial District', 'Alamo Square')])

# If you meet John first, then Stephanie
solver.add(Or(
    And(
        t_start_john >= arrival_time + travel_times[('Embarcadero', 'Alamo Square')],
        t_start_stephanie >= t_end_john + travel_times[('Alamo Square', 'Financial District')]
    )
))

# Ensure the meeting times are within the availability windows
solver.add(t_start_stephanie >= 8 * 60 + 15)
solver.add(t_end_stephanie <= 11 * 60 + 30)
solver.add(t_start_john >= 10 * 60 + 15)
solver.add(t_end_john <= 20 * 60 + 45)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Meet Stephanie from {model[t_start_stephanie].as_long()} to {model[t_end_stephanie].as_long()}")
    print(f"Meet John from {model[t_start_john].as_long()} to {model[t_end_john].as_long()}")
else:
    print("No solution found.")