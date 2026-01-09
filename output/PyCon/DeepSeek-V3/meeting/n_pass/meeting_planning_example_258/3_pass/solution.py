from constraint import Problem

# Define the minimum durations for each person
betty_min = 20
david_min = 25
barbara_min = 15

# Create the constraint problem
problem = Problem()

# Define the order of people
order = [0, 1, 2]  # betty, david, barbara

# Create a list of minimum durations for easy access
min_durations = [betty_min, david_min, barbara_min]

# Add variables for each person's duration
for i in order:
    problem.addVariable(f'dur_{i}', [min_durations[i]])

print("Variables added successfully!")