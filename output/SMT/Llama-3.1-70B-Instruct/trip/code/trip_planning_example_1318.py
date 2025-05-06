from z3 import *

# Define the cities and their stay durations
cities = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
durations = {'Oslo': 2, 'Helsinki': 2, 'Edinburgh': 3, 'Riga': 2, 'Tallinn': 5, 'Budapest': 5, 'Vilnius': 5, 'Porto': 5, 'Geneva': 4}

# Define the direct flights between cities
direct_flights = {
    'Porto': ['Oslo'],
    'Edinburgh': ['Budapest'],
    'Edinburgh': ['Geneva'],
    'Riga': ['Tallinn'],
    'Edinburgh': ['Porto'],
    'Vilnius': ['Helsinki'],
    'Tallinn': ['Vilnius'],
    'Riga': ['Oslo'],
    'Geneva': ['Oslo'],
    'Edinburgh': ['Oslo'],
    'Edinburgh': ['Helsinki'],
    'Vilnius': ['Oslo'],
    'Riga': ['Helsinki'],
    'Budapest': ['Geneva'],
    'Helsinki': ['Budapest'],
    'Helsinki': ['Oslo'],
    'Edinburgh': ['Riga'],
    'Tallinn': ['Helsinki'],
    'Geneva': ['Porto'],
    'Budapest': ['Oslo'],
    'Helsinki': ['Geneva'],
    'Riga': ['Vilnius'],
    'Tallinn': ['Oslo']
}

# Define the constraints
def define_constraints():
    # Define the variables
    city_vars = [Int(f'city_{i}') for i in range(25)]
    for var in city_vars:
        var.domain(cities)

    # Define the constraints
    constraints = []
    constraints.append(Or([city_vars[23] == 'Oslo', city_vars[24] == 'Oslo']))  # Meet a friend in Oslo between day 24 and 25
    constraints.append(Or([city_vars[3] == 'Tallinn', city_vars[4] == 'Tallinn', city_vars[5] == 'Tallinn', city_vars[6] == 'Tallinn', city_vars[7] == 'Tallinn']))  # Attend wedding in Tallinn between day 4 and 8

    # Stay in each city for the required duration
    for city, duration in durations.items():
        constraints.append(Sum([If(city_vars[i] == city, 1, 0) for i in range(25)]) == duration)

    # Ensure that the trip plan is feasible (i.e., only take direct flights)
    for i in range(24):
        constraints.append(Or([And(city_vars[i] == from_city, city_vars[i+1] == to_city) for from_city, to_cities in direct_flights.items() for to_city in to_cities]))

    # Ensure that the trip plan is connected (i.e., no gaps in the trip plan)
    constraints.append(Distinct([city_vars[i] for i in range(25)]))

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