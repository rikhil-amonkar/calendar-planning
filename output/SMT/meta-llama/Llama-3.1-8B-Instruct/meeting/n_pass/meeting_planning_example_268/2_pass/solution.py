from z3 import *

# Define the travel times
travel_times = {
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14
}

# Define the constraints
s = Optimize()

# Define the variables
visit_timothy = Bool('visit_timothy')
visit_mark = Bool('visit_mark')
visit_joseph = Bool('visit_joseph')
time_at_alamo_square = Int('time_at_alamo_square')
time_at_presidio = Int('time_at_presidio')
time_at_russian_hill = Int('time_at_russian_hill')

# Add the constraints
s.add(If(visit_timothy, 105, 0) >= 105)
s.add(If(visit_mark, 60, 0) >= 60)
s.add(If(visit_joseph, 60, 0) >= 60)
s.add(time_at_alamo_square >= 0)
s.add(time_at_alamo_square <= 360)
s.add(time_at_presidio >= 0)
s.add(time_at_presidio <= 375)
s.add(time_at_russian_hill >= 0)
s.add(time_at_russian_hill <= 390)
s.add(If(visit_timothy, time_at_alamo_square - 720 >= 0, True))
s.add(If(visit_mark, time_at_presidio - 675 >= 0, True))
s.add(If(visit_joseph, time_at_russian_hill - 630 >= 0, True))
s.add(If(visit_timothy, time_at_alamo_square - 9*60 + travel_times[('Golden Gate Park', 'Alamo Square')] >= 0, True))
s.add(If(visit_mark, time_at_presidio - 9*60 - 9*60 + travel_times[('Golden Gate Park', 'Presidio')] >= 0, True))
s.add(If(visit_joseph, time_at_russian_hill - 9*60 - 4*60 + travel_times[('Golden Gate Park', 'Russian Hill')] >= 0, True))
s.add(If(visit_timothy, time_at_alamo_square - 9*60 - 9*60 + travel_times[('Alamo Square', 'Presidio')] >= 0, True))
s.add(If(visit_mark, time_at_presidio - 9*60 + travel_times[('Presidio', 'Golden Gate Park')] >= 0, True))
s.add(If(visit_joseph, time_at_russian_hill - 9*60 + travel_times[('Russian Hill', 'Golden Gate Park')] >= 0, True))
s.add(If(visit_timothy, time_at_alamo_square - 9*60 + travel_times[('Alamo Square', 'Golden Gate Park')] >= 0, True))
s.add(If(visit_mark, time_at_presidio - 9*60 + travel_times[('Presidio', 'Alamo Square')] >= 0, True))
s.add(If(visit_joseph, time_at_russian_hill - 9*60 + travel_times[('Russian Hill', 'Alamo Square')] >= 0, True))
s.add(If(visit_timothy, time_at_alamo_square - 9*60 + travel_times[('Alamo Square', 'Russian Hill')] >= 0, True))
s.add(If(visit_mark, time_at_presidio - 9*60 + travel_times[('Presidio', 'Russian Hill')] >= 0, True))
s.add(If(visit_joseph, time_at_russian_hill - 9*60 + travel_times[('Russian Hill', 'Presidio')] >= 0, True))

# Define the objective function
s.minimize(If(visit_timothy, 0, 1) + If(visit_mark, 0, 1) + If(visit_joseph, 0, 1))

# Solve the optimization problem
solution = s.check()

# Print the solution
if solution == sat:
    m = s.model()
    print("Visit Timothy:", m[visit_timothy])
    print("Visit Mark:", m[visit_mark])
    print("Visit Joseph:", m[visit_joseph])
    print("Time at Alamo Square:", m[time_at_alamo_square])
    print("Time at Presidio:", m[time_at_presidio])
    print("Time at Russian Hill:", m[time_at_russian_hill])
else:
    print("No solution found")