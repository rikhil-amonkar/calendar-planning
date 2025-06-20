from z3 import *

# Define the variables
start_time = 0
end_time = 1440  # 1440 minutes in a day
friends = [
    {"name": "Matthew", "location": "Bayview", "start_time": 435, "end_time": 600, "min_time": 120},
    {"name": "Karen", "location": "Chinatown", "start_time": 465, "end_time": 585, "min_time": 90},
    {"name": "Sarah", "location": "Alamo Square", "start_time": 480, "end_time": 585, "min_time": 105},
    {"name": "Jessica", "location": "Nob Hill", "start_time": 270, "end_time": 405, "min_time": 120},
    {"name": "Stephanie", "location": "Presidio", "start_time": 90, "end_time": 165, "min_time": 60},
    {"name": "Mary", "location": "Union Square", "start_time": 285, "end_time": 570, "min_time": 60},
    {"name": "Charles", "location": "The Castro", "start_time": 270, "end_time": 600, "min_time": 105},
    {"name": "Nancy", "location": "North Beach", "start_time": 165, "end_time": 480, "min_time": 15},
    {"name": "Thomas", "location": "Fisherman's Wharf", "start_time": 90, "end_time": 420, "min_time": 30},
    {"name": "Brian", "location": "Marina District", "start_time": 75, "end_time": 360, "min_time": 60},
]

# Define the locations and their distances from Embarcadero
locations = {
    "Embarcadero": 0,
    "Bayview": 21,
    "Chinatown": 7,
    "Alamo Square": 19,
    "Nob Hill": 10,
    "Presidio": 20,
    "Union Square": 10,
    "The Castro": 25,
    "North Beach": 5,
    "Fisherman's Wharf": 6,
    "Marina District": 12,
}

# Create the solver
s = Optimize()

# Define the decision variables
x = [Bool(f"visit_{i}") for i in range(len(friends))]
y = [Int(f"meet_{i}") for i in range(len(friends))]
z = [Int(f"travel_{i}") for i in range(len(friends))]

# Define the constraints
for i in range(len(friends)):
    s.add(If(x[i], y[i], 0) >= friends[i]["min_time"])  # If visit, then meet for at least min_time
    s.add(z[i] >= abs(locations[friends[i]["location"]] - locations["Embarcadero"]))  # Travel time is at least distance
    s.add(y[i] >= 0)  # Meeting time is non-negative
    s.add(y[i] <= 1440)  # Meeting time is within 1440 minutes

# Define the objective function
maximize = Maximize(Sum([If(x[i], y[i], 0) for i in range(len(friends))]))  # Maximize total meeting time
s.add(maximize)

# Solve the problem
s.check()
model = s.model()

# Print the solution
print("SOLUTION:")
for i in range(len(friends)):
    if model[x[i]]:
        print(f"Visit {friends[i]['name']}: {model[z[i]].as_long()} minutes")
        print(f"Meet {friends[i]['name']}: {model[y[i]].as_long()} minutes")
    else:
        print(f"Skip {friends[i]['name']}")
    print()