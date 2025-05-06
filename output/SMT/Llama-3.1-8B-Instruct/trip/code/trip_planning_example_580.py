from z3 import *

def schedule_trip():
    # Define the cities
    cities = ['Paris', 'Oslo', 'Geneva', 'Porto', 'Reykjavik']

    # Define the days
    days = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

    # Define the direct flights
    direct_flights = {
        ('Paris', 'Oslo'): 1,
        ('Geneva', 'Oslo'): 1,
        ('Porto', 'Paris'): 1,
        ('Geneva', 'Paris'): 1,
        ('Geneva', 'Porto'): 1,
        ('Paris', 'Reykjavik'): 1,
        ('Reykjavik', 'Oslo'): 1,
        ('Porto', 'Oslo'): 1,
    }

    # Define the constraints
    constraints = []
    for day in days:
        for city1 in cities:
            for city2 in cities:
                if city1!= city2:
                    constraints.append(Not(And(day >= 1, day <= 23, city1 in cities, city2 in cities, (city1, city2) in direct_flights)))

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
        for day in days:
            trip_plan.append(model[('city', day).as_long()])
        print(trip_plan)
    else:
        print("No solution found")

# Example usage
schedule_trip()