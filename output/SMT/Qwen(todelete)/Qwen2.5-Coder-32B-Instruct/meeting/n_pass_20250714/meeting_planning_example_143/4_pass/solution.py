from z3 import *

# Define the time variables for each location visit
north_beach_start = Int('north_beach_start')
pacific_heights_start = Int('pacific_heights_start')
embarcadero_start = Int('embarcadero_start')

# Define the durations for each meeting
mark_meeting_duration = Int('mark_meeting_duration')
karen_meeting_duration = Int('karen_meeting_duration')

# Create a solver instance
solver = Solver()

# Add constraints based on the problem statement
# Arrival time at North Beach
solver.add(north_beach_start == 9 * 60)  # 9:00 AM in minutes

# Meeting Mark constraints
solver.add(embarcadero_start == 13 * 60)  # Start meeting Mark at 1:00 PM
solver.add(mark_meeting_duration == 120)  # Meeting duration of 120 minutes

# Meeting Karen constraints
solver.add(pacific_heights_start == 18 * 45)  # Start meeting Karen at 6:45 PM
solver.add(karen_meeting_duration == 90)  # Meeting duration of 90 minutes

# Travel time constraints
# From North Beach to Embarcadero
solver.add(embarcadero_start >= north_beach_start + 6)
# From Embarcadero to Pacific Heights
solver.add(pacific_heights_start >= embarcadero_start + 11)

if solver.check() == sat:
    model = solver.model()
    nb_start = model[north_beach_start].as_long()
    ph_start = model[pacific_heights_start].as_long()
    e_start = model[embarcadero_start].as_long()
    m_duration = model[mark_meeting_duration].as_long()
    k_duration = model[karen_meeting_duration].as_long()

    print(f"SOLUTION:")
    print(f"Visit North Beach at {nb_start // 60}:{nb_start % 60:02d}")
    print(f"Visit Embarcadero at {e_start // 60}:{e_start % 60:02d} for {m_duration} minutes")
    print(f"Visit Pacific Heights at {ph_start // 60}:{ph_start % 60:02d} for {k_duration} minutes")
else:
    print("No solution found.")