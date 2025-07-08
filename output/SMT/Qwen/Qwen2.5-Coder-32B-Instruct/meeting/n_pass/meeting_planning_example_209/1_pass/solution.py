from z3 import *

# Define the time variables for arriving at each location
t_sunset = Int('t_sunset')
t_chinatown = Int('t_chinatown')
t_russian_hill = Int('t_russian_hill')
t_north_beach = Int('t_north_beach')

# Define the solver
solver = Solver()

# Initial constraint: you arrive at Sunset District at 9:00AM (540 minutes after midnight)
solver.add(t_sunset == 540)

# Travel time constraints
solver.add(t_chinatown >= t_sunset + 30)  # Sunset District to Chinatown
solver.add(t_russian_hill >= t_sunset + 24)  # Sunset District to Russian Hill
solver.add(t_north_beach >= t_sunset + 29)  # Sunset District to North Beach

solver.add(t_sunset >= t_chinatown + 29)  # Chinatown to Sunset District
solver.add(t_russian_hill >= t_chinatown + 7)  # Chinatown to Russian Hill
solver.add(t_north_beach >= t_chinatown + 3)  # Chinatown to North Beach

solver.add(t_sunset >= t_russian_hill + 23)  # Russian Hill to Sunset District
solver.add(t_chinatown >= t_russian_hill + 9)  # Russian Hill to Chinatown
solver.add(t_north_beach >= t_russian_hill + 5)  # Russian Hill to North Beach

solver.add(t_sunset >= t_north_beach + 27)  # North Beach to Sunset District
solver.add(t_chinatown >= t_north_beach + 6)  # North Beach to Chinatown
solver.add(t_russian_hill >= t_north_beach + 4)  # North Beach to Russian Hill

# Availability constraints for friends
# Anthony: 1:15PM to 2:30PM (795 to 930 minutes after midnight), meet for at least 60 minutes
solver.add(Or(t_chinatown < 795, t_chinatown + 60 > 930))

# Rebecca: 7:30PM to 9:15PM (1230 to 1395 minutes after midnight), meet for at least 105 minutes
solver.add(Or(t_russian_hill < 1230, t_russian_hill + 105 > 1395))

# Melissa: 8:15AM to 1:30PM (495 to 810 minutes after midnight), meet for at least 105 minutes
solver.add(Or(t_north_beach < 495, t_north_beach + 105 > 810))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Arrive at Sunset District: {model[t_sunset]} minutes after midnight (9:00AM)")
    print(f"Arrive at Chinatown: {model[t_chinatown]} minutes after midnight ({model[t_chinatown] // 60}:{model[t_chinatown] % 60:02d}AM/PM)")
    print(f"Arrive at Russian Hill: {model[t_russian_hill]} minutes after midnight ({model[t_russian_hill] // 60}:{model[t_russian_hill] % 60:02d}AM/PM)")
    print(f"Arrive at North Beach: {model[t_north_beach]} minutes after midnight ({model[t_north_beach] // 60}:{model[t_north_beach] % 60:02d}AM/PM)")
else:
    print("No solution found.")