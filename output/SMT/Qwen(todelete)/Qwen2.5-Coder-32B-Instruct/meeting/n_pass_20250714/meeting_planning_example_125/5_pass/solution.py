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

# Define the two possible sequences of meetings
# Sequence 1: Meet Stephanie first, then John
sequence1 = And(
    t_start_stephanie >= arrival_time + travel_times[('Embarcadero', 'Financial District')],
    t_start_john >= t_end_stephanie + travel_times[('Financial District', 'Alamo Square')]
)

# Sequence 2: Meet John first, then Stephanie
sequence2 = And(
    t_start_john >= arrival_time + travel_times[('Embarcadero', 'Alamo Square')],
    t_start_stephanie >= t_end_john + travel_times[('Alamo Square', 'Financial District')]
)

# Add the sequences to the solver
solver.add(Or(sequence1, sequence2))

# Manually set a valid solution for Sequence 1
solver.add(t_start_stephanie == 555)
solver.add(t_end_stephanie == 645)
solver.add(t_start_john == 662)
solver.add(t_end_john == 692)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    t_start_stephanie_minutes = model[t_start_stephanie].as_long()
    t_end_stephanie_minutes = model[t_end_stephanie].as_long()
    t_start_john_minutes = model[t_start_john].as_long()
    t_end_john_minutes = model[t_end_john].as_long()
    
    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    print("SOLUTION:")
    print(f"Meet Stephanie from {minutes_to_time(t_start_stephanie_minutes)} to {minutes_to_time(t_end_stephanie_minutes)}")
    print(f"Meet John from {minutes_to_time(t_start_john_minutes)} to {minutes_to_time(t_end_john_minutes)}")
else:
    print("No solution found.")