from z3 import *

# Define the travel distances in minutes
distances = {
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
start_time = 0
timothy_arrives = 12
timothy_leaves = 4*60 + 15
mark_arrives = 6*60 + 45
mark_leaves = 9*60
joseph_arrives = 4*60 + 45
joseph_leaves = 9*60 + 30
min_timothy_time = 105
min_mark_time = 60
min_joseph_time = 60

# Define the variables
x = Int('x')
y = Int('y')
z = Int('z')

# Define the constraints
constraints = [
    x >= start_time,
    y >= start_time,
    z >= start_time,
    x + distances[('Golden Gate Park', 'Alamo Square')] <= y,
    y + distances[('Alamo Square', 'Presidio')] <= z,
    z + distances[('Presidio', 'Russian Hill')] <= 24*60,  # Assume you leave Presidio by 6:00PM
    x + distances[('Golden Gate Park', 'Alamo Square')] + min_timothy_time <= timothy_arrives,
    y + distances[('Alamo Square', 'Presidio')] + min_mark_time <= mark_arrives,
    z + distances[('Presidio', 'Russian Hill')] + min_joseph_time <= joseph_arrives
]

# Solve the constraints
s = Optimize()
s.add(constraints)
s.add(x + distances[('Golden Gate Park', 'Alamo Square')] + min_timothy_time <= timothy_leaves)
s.add(y + distances[('Alamo Square', 'Presidio')] + min_mark_time <= mark_leaves)
s.add(z + distances[('Presidio', 'Russian Hill')] + min_joseph_time <= joseph_leaves)
s.minimize(x + y + z)

# Check if an optimal solution exists
if s.check() == sat:
    model = s.model()
    print(f"Optimal schedule: {model[x]}:00AM - {model[x] + distances[('Golden Gate Park', 'Alamo Square')]}:00AM (Timothy), {model[y]}:00AM - {model[y] + distances[('Alamo Square', 'Presidio')]}:00AM (Mark), {model[z]}:00AM - {model[z] + distances[('Presidio', 'Russian Hill')]}:00AM (Joseph)")
else:
    print("No optimal solution exists.")