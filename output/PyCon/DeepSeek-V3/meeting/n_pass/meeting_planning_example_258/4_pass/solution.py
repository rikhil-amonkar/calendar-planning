from constraint import Problem

# Define the minimum durations for each person
betty_min = 20
david_min = 25
barbara_min = 15

# Create the constraint problem
problem = Problem()

# Define the order of people
people = ['betty', 'david', 'barbara']
min_durations = [betty_min, david_min, barbara_min]

# Add variables for each person's duration (using minimum durations as starting point)
# Let's allow durations up to 60 minutes for flexibility
for i, person in enumerate(people):
    problem.addVariable(f'{person}_duration', range(min_durations[i], 61))

# Add constraint: total duration must be exactly 60 minutes
problem.addConstraint(
    lambda betty, david, barbara: betty + david + barbara == 60,
    ['betty_duration', 'david_duration', 'barbara_duration']
)

# Add constraint: each person must use at least their minimum duration
# (This is already enforced by the variable domains, but we can add explicit constraints)
for i, person in enumerate(people):
    problem.addConstraint(
        lambda dur, min_dur=min_durations[i]: dur >= min_dur,
        [f'{person}_duration']
    )

# Solve the problem
solutions = problem.getSolutions()

if solutions:
    print("Valid plan found!")
    print("\nExercise schedule:")
    print("=" * 30)
    
    # Use the first valid solution
    solution = solutions[0]
    total = 0
    
    for person in people:
        duration = solution[f'{person}_duration']
        total += duration
        print(f"{person.capitalize()}: {duration} minutes")
    
    print("=" * 30)
    print(f"Total: {total} minutes")
    
    # Verify all constraints are met
    print("\nConstraint verification:")
    print(f"- Betty ≥ {betty_min} minutes: {solution['betty_duration'] >= betty_min}")
    print(f"- David ≥ {david_min} minutes: {solution['david_duration'] >= david_min}")
    print(f"- Barbara ≥ {barbara_min} minutes: {solution['barbara_duration'] >= barbara_min}")
    print(f"- Total = 60 minutes: {total == 60}")
    
else:
    print("No valid plan found that satisfies all constraints.")