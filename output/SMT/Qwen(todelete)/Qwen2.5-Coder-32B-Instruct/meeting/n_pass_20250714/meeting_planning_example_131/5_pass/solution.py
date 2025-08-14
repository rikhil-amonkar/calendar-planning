from z3 import *

# Define the time variables for arrival at each location
t_ph = Int('t_ph')  # Arrival time at Pacific Heights
t_pres = Int('t_pres')  # Arrival time at Presidio
t_md = Int('t_md')  # Arrival time at Marina District

# Create a solver instance
solver = Solver()

# Add constraints for initial arrival time
solver.add(t_ph == 9 * 60)  # Convert 9:00AM to minutes since midnight

# Add constraints for travel times
solver.add(t_pres >= t_ph + 11)  # Travel from PH to Presidio takes 11 minutes
solver.add(t_md >= t_ph + 6)     # Travel from PH to Marina District takes 6 minutes
solver.add(t_ph >= t_pres + 11) # Travel from Presidio to PH takes 11 minutes
solver.add(t_md >= t_pres + 10) # Travel from Presidio to Marina District takes 10 minutes
solver.add(t_ph >= t_md + 7)    # Travel from Marina District to PH takes 7 minutes
solver.add(t_pres >= t_md + 10) # Travel from Marina District to Presidio takes 10 minutes

# Add constraints for meeting Jason at Presidio
jason_start = 10 * 60  # 10:00AM in minutes
jason_end = 16 * 60 + 15  # 4:15PM in minutes
solver.add(t_pres == jason_start)  # Arrive at Presidio at 10:00AM
solver.add(t_pres + 90 <= jason_end)  # Must stay for at least 90 minutes

# Add constraints for meeting Kenneth at Marina District
kenneth_start = 15 * 60 + 30  # 3:30PM in minutes
kenneth_end = 16 * 60 + 45  # 4:45PM in minutes
solver.add(t_md == kenneth_start)  # Arrive at Marina District at 3:30PM
solver.add(t_md + 45 <= kenneth_end)  # Must stay for at least 45 minutes

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print("Schedule found:")
    print(f"Arrive at Pacific Heights at {model[t_ph].as_long()} minutes (or {model[t_ph].as_long() // 60}:{model[t_ph].as_long() % 60:02d} AM/PM)")
    print(f"Arrive at Presidio at {model[t_pres].as_long()} minutes (or {model[t_pres].as_long() // 60}:{model[t_pres].as_long() % 60:02d} AM/PM)")
    print(f"Arrive at Marina District at {model[t_md].as_long()} minutes (or {model[t_md].as_long() // 60}:{model[t_md].as_long() % 60:02d} AM/PM)")
else:
    print("No feasible schedule found.")