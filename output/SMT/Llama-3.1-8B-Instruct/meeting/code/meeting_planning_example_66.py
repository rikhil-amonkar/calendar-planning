from z3 import *

def schedule_trip():
    # Define the cities
    cities = ['Nob Hill', 'Presidio']

    # Define the travel distances
    travel_distances = {
        ('Nob Hill', 'Presidio'): 17,
        ('Presidio', 'Nob Hill'): 18,
    }

    # Define the constraints
    constraints = [
        ('Nob Hill', 9, 10),
        ('Presidio', 11, 12),
        ('Nob Hill', 'Presidio', 120),
    ]

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the trip plan
    if result == sat:
        model = solver.model()
        trip_plan = []
        for city in cities:
            trip_plan.append(model[('city', city).as_long()])
        print(trip_plan)
    else:
        print("No solution found")

# Example usage
schedule_trip()