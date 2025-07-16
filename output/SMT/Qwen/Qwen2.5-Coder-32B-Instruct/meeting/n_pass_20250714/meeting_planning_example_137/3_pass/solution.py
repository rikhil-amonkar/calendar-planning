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

# Define boolean variables to indicate the order of visits
visit_chinatown_first = Bool('visit_chinatown_first')
visit_golden_gate_park_first = Bool('visit_golden_gate_park_first')

# Ensure only one order is chosen
solver.add(visit_chinatown_first != visit_golden_gate_park_first)

# Constraints for visiting Chinatown first
solver.add(Implies(visit_chinatown_first,
                   And(t_chinatown_start == start_time + travel_fd_to_ch,
                       t_golden_gate_park_start >= t_chinatown_end + travel_ch_to_ggp,
                       t_golden_gate_park_start >= start_time + travel_fd_to_ggp)))

# Constraints for visiting Golden Gate Park first
solver.add(Implies(visit_golden_gate_park_first,
                   And(t_golden_gate_park_start == start_time + travel_fd_to_ggp,
                       t_chinatown_start >= t_golden_gate_park_end + travel_ggp_to_ch,
                       t_chinatown_start >= start_time + travel_fd_to_ch)))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Visit Chinatown from {model[t_chinatown_start]} to {model[t_chinatown_end]}")
    print(f"Visit Golden Gate Park from {model[t_golden_gate_park_start]} to {model[t_golden_gate_park_end]}")
    print(f"Order of visits: {'Chinatown first' if model[visit_chinatown_first] else 'Golden Gate Park first'}")
else:
    print("No solution found")