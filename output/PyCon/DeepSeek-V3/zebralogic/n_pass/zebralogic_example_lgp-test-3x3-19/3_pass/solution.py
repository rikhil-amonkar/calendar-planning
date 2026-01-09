from constraint import Problem

# Create the problem instance
problem = Problem()

# Define variables for each house (1-5)
houses = [1, 2, 3, 4, 5]

# Add variables for names and genres
names = ["Arnold", "Boris", "Catherine", "Dmitri", "Elena"]
genres = ["mystery", "romance", "science fiction", "thriller", "fantasy"]

for house in houses:
    problem.addVariable(f"name_{house}", names)
    problem.addVariable(f"genre_{house}", genres)

# Add constraints
# All names and genres must be different
problem.addConstraint(lambda *names: len(set(names)) == len(names), [f"name_{h}" for h in houses])
problem.addConstraint(lambda *genres: len(set(genres)) == len(genres), [f"genre_{h}" for h in houses])

# Arnold reads mystery
for house in houses:
    problem.addConstraint(lambda name, genre, h=house: not (name == "Arnold") or (genre == "mystery"), 
                         [f"name_{h}", f"genre_{h}"])

# Get and print solutions
solutions = problem.getSolutions()
print(f"Number of solutions: {len(solutions)}")
for solution in solutions:
    print("\nSolution:")
    for house in sorted(houses):
        print(f"House {house}: {solution[f'name_{house}']} reads {solution[f'genre_{house}']}")