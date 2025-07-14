from z3 import *

# Define the solver
solver = Solver()

# Define the time variables for each location visit
t_chinatown_start = Int('t_chinatown_start')
t_chinatown_end = Int('t_chinatown_end')
t_golden_gate_park_start = Int('t_golden_gate_park_start')
t_golden_gate_park_end = Int('t_golden_gate_park_end')

# Constraints for arrival and departure times
solver.add(t_chinatown_start >= 12 * 60)  # 12:00 PM in minutes
solver.add(t_chinatown_end <= 15 * 60)    # 3:00 PM in minutes
solver.add(t_chinatown_end - t_chinatown_start >= 90)  # Minimum 90 minutes with Kenneth

solver.add(t_golden_gate_park_start >= 8 * 60 + 15)  # 8:15 AM in minutes
solver.add(t_golden_gate_park_end <= 19 * 60)        # 7:00 PM in minutes
solver.add(t_golden_gate_park_end - t_golden_gate_park_start >= 45)  # Minimum 45 minutes with Barbara

# Travel times in minutes
travel_fd_to_ch = 5
travel_ch_to_fd = 5
travel_fd_to_ggp = 23
travel_ggp_to_fd = 26
travel_ch_to_ggp = 23
travel_ggp_to_ch = 23

# Start time at Financial District
start_time = 9 * 60  # 9:00 AM in minutes

# Add constraints for travel times
# If visiting Chinatown first
solver.add(Or(
    And(t_chinatown_start == start_time + travel_fd_to_ch,
        t_golden_gate_park_start >= t_chinatown_end + travel_ch_to_ggp),
    And(t_chinatown_start == start_time + travel_fd_to_ch,
        t_golden_gate_park_start >= start_time + travel_fd_to_ggp)
))

# If visiting Golden Gate Park first
solver.add(Or(
    And(t_golden_gate_park_start == start_time + travel_fd_to_ggp,
        t_chinatown_start >= t_golden_gate_park_end + travel_ggp_to_ch),
    And(t_golden_gate_park_start == start_time + travel_fd_to_ggp,
        t_chinatown_start >= start_time + travel_fd_to_ch)
))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Meet Kenneth at Chinatown from {model[t_chinatown_start]} to {model[t_chinatown_end]}")
    print(f"Meet Barbara at Golden Gate Park from {model[t_golden_gate_park_start]} to {model[t_golden_gate_park_end]}")
else:
    print("No solution found")