from z3 import *

# Define the cities and their stay durations
cities = ['Mykonos', 'Krakow', 'Vilnius', 'Helsinki', 'Dubrovnik', 'Oslo', 'Madrid', 'Paris']
durations = {'Mykonos': 4, 'Krakow': 5, 'Vilnius': 2, 'Helsinki': 2, 'Dubrovnik': 3, 'Oslo': 2, 'Madrid': 5, 'Paris': 2}

# Define the direct flights between cities
direct_flights = {
    'Oslo': ['Krakow'],
    'Oslo': ['Paris'],
    'Paris': ['Madrid'],
    'Helsinki': ['Vilnius'],
    'Oslo': ['Madrid'],
    'Oslo': ['Helsinki'],
    'Helsinki': ['Krakow'],
    'Dubrovnik': ['Helsinki'],
    'Dubrovnik': ['Madrid'],
    'Oslo': ['Dubrovnik'],
    'Krakow': ['Paris'],
    'Madrid': ['Mykonos'],
    'Oslo': ['Vilnius'],
    'Krakow': ['Vilnius'],
    'Helsinki': ['Paris'],
    'Vilnius': ['Paris'],
    'Helsinki': ['Madrid']
}

# Define the constraints
def define_constraints():
    # Define the variables
    city_vars = [Int(f'city_{i}') for i in range(18)]
    for var in city_vars:
        var.domain(cities)

    # Define the constraints
    constraints = []
    constraints.append(Or([city_vars[14] == 'Mykonos', city_vars[15] == 'Mykonos', city_vars[16] == 'Mykonos', city_vars[17] == 'Mykonos']))  # Visit relatives in Mykonos between day 15 and 18
    constraints.append(Or([city_vars[1] == 'Dubrovnik', city_vars[2] == 'Dubrovnik', city_vars[3] == 'Dubrovnik']))  # Attend annual show in Dubrovnik between day 2 and 4
    constraints.append(Or([city_vars[0] == 'Oslo', city_vars[1] == 'Oslo']))  # Meet friends at Oslo between day 1 and 2

    # Stay in each city for the required duration
    for city, duration in durations.items():
        constraints.append(Sum([If(city_vars[i] == city, 1, 0) for i in range(18)]) == duration)

    # Ensure that the trip plan is feasible (i.e., only take direct flights)
    for i in range(17):
        constraints.append(Or([And(city_vars[i] == from_city, city_vars[i+1] == to_city) for from_city, to_cities in direct_flights.items() for to_city in to_cities]))

    # Ensure that the trip plan is connected (i.e., no gaps in the trip plan)
    constraints.append(Distinct([city_vars[i] for i in range(18)]))

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