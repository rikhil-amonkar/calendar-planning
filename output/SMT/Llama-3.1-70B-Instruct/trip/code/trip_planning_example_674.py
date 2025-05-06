from z3 import *

# Define the cities and their stay durations
cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
durations = {'Helsinki': 2, 'Warsaw': 3, 'Madrid': 4, 'Split': 4, 'Reykjavik': 2, 'Budapest': 4}

# Define the direct flights between cities
direct_flights = {
    'Helsinki': ['Reykjavik'],
    'Budapest': ['Warsaw'],
    'Madrid': ['Split'],
    'Helsinki': ['Split'],
    'Helsinki': ['Madrid'],
    'Helsinki': ['Budapest'],
    'Reykjavik': ['Warsaw'],
    'Helsinki': ['Warsaw'],
    'Madrid': ['Budapest'],
    'Budapest': ['Reykjavik'],
    'Madrid': ['Warsaw'],
    'Warsaw': ['Split'],
    'Reykjavik': ['Madrid']
}

# Define the constraints
def define_constraints():
    # Define the variables
    city_vars = [Int(f'city_{i}') for i in range(14)]
    for var in city_vars:
        var.domain(cities)

    # Define the constraints
    constraints = []
    constraints.append(Or([city_vars[0] == 'Helsinki', city_vars[1] == 'Helsinki']))  # Attend workshop in Helsinki between day 1 and 2
    constraints.append(Or([city_vars[8] == 'Reykjavik', city_vars[9] == 'Reykjavik']))  # Meet a friend in Reykjavik between day 8 and 9
    constraints.append(Or([city_vars[8] == 'Warsaw', city_vars[9] == 'Warsaw', city_vars[10] == 'Warsaw']))  # Visit relatives in Warsaw between day 9 and 11

    # Stay in each city for the required duration
    for city, duration in durations.items():
        constraints.append(Sum([If(city_vars[i] == city, 1, 0) for i in range(14)]) == duration)

    # Ensure that the trip plan is feasible (i.e., only take direct flights)
    for i in range(13):
        constraints.append(Or([And(city_vars[i] == from_city, city_vars[i+1] == to_city) for from_city, to_cities in direct_flights.items() for to_city in to_cities]))

    # Ensure that the trip plan is connected (i.e., no gaps in the trip plan)
    constraints.append(Distinct([city_vars[i] for i in range(14)]))

    return city_vars, constraints

# Solve the constraints
def solve_constraints(city_vars, constraints):
    solver = Solver()
    for constraint in constraints:
        solver.add(constraint)
    if solver.check() == sat:
        model = solver.model()
        trip_plan = [model.evaluate(city_var).as_string() for city_var in city_vars]
        return trip_plan
    else:
        return None

# Main function
def main():
    city_vars, constraints = define_constraints()
    trip_plan = solve_constraints(city_vars, constraints)
    if trip_plan is not None:
        print('Trip Plan:')
        for i, city in enumerate(trip_plan):
            print(f'Day {i+1}: {city}')
    else:
        print('No trip plan found.')

if __name__ == '__main__':
    main()