from z3 import *

# Define the travel times
travel_times = {
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18
}

# Define the constraints
def meet_with_betty(x, y):
    return And(x >= 10.25, x <= 21.75, y >= 45)

def meet_with_david(x, y):
    return And(x >= 13.5, x <= 19.75, y >= 90)

def meet_with_barbara(x, y):
    return And(x >= 9.25, x <= 20.75, y >= 120)

# Define the variables
x = [Int(f'x_{i}') for i in range(4)]  # start time for each friend
y = [Int(f'y_{i}') for i in range(4)]  # duration of meeting with each friend
locations = ['Embarcadero', 'Presidio', 'Richmond District', 'Fisherman\'s Wharf']
locations_map = {locations[i]: i for i in range(len(locations))}
locations_map_inverse = {v: k for k, v in locations_map.items()}

# Define the solver
s = Solver()

# Add constraints
s.add(x[0] == 9 * 60)  # start at Embarcadero at 9:00AM
for i in range(3):
    s.add(y[i] > 0)  # duration of meeting must be positive
    s.add(x[i+1] > x[i])  # start time of meeting must be after end of previous meeting
    s.add(x[i+1] - x[i] >= y[i])  # start time of meeting must be after end of meeting
    if i == 0:
        s.add(x[i+1] - x[i] >= 10.25)  # travel time must not be less than 10.25 hours
        s.add(x[i+1] - x[i] <= 21.75)  # travel time must not exceed 21.75 hours
    elif i == 1:
        s.add(x[i+1] - x[i] >= 13.5)  # travel time must not be less than 13.5 hours
        s.add(x[i+1] - x[i] <= 19.75)  # travel time must not exceed 19.75 hours
    else:
        s.add(x[i+1] - x[i] >= 9.25)  # travel time must not be less than 9.25 hours
        s.add(x[i+1] - x[i] <= 20.75)  # travel time must not exceed 20.75 hours
    s.add(meet_with_betty(x[i], y[i])) if i == 0 else s.add(meet_with_david(x[i], y[i])) if i == 1 else s.add(meet_with_barbara(x[i], y[i]))
    s.add(y[i] <= 12 * 60)  # duration of meeting must not exceed 12 hours

# Solve the problem
s.check()
model = s.model()

# Print the solution
print('SOLUTION:')
for i in range(4):
    print(f'Meet with {["Betty", "David", "Barbara"][i]} from {model[x[i]].as_real().as_float()} to {(model[x[i]+1].as_real().as_float())} for {(model[y[i]].as_real().as_float())} minutes')