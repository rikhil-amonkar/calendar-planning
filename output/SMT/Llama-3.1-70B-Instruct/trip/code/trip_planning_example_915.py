from z3 import *

# Define the cities and their stay durations
cities = ['Bucharest', 'Venice', 'Prague', 'Frankfurt', 'Zurich', 'Florence', 'Tallinn']
durations = {'Bucharest': 3, 'Venice': 5, 'Prague': 4, 'Frankfurt': 5, 'Zurich': 5, 'Florence': 5, 'Tallinn': 5}

# Define the direct flights between cities
direct_flights = {
    'Prague': ['Tallinn'],
    'Prague': ['Zurich'],
    'Florence': ['Prague'],
    'Frankfurt': ['Bucharest'],
    'Frankfurt': ['Venice'],
    'Prague': ['Bucharest'],
    'Bucharest': ['Zurich'],
    'Tallinn': ['Frankfurt'],
    'Zurich': ['Florence'],
    'Frankfurt': ['Zurich'],
    'Zurich': ['Venice'],
    'Florence': ['Frankfurt'],
    'Prague': ['Frankfurt'],
    'Tallinn': ['Zurich']
}

# Define the constraints
def define_constraints():
    # Define the variables
    city_vars = [Int(f'city_{i}') for i in range(26)]
    for var in city_vars:
        var.domain(cities)

    # Define the constraints
    constraints = []
    constraints.append(Or([city_vars[7] == 'Tallinn', city_vars[8] == 'Tallinn', city_vars[9] == 'Tallinn', city_vars[10] == 'Tallinn', city_vars[11] == 'Tallinn']))  # Meet friends at Tallinn between day 8 and 12
    constraints.append(Or([city_vars[11] == 'Frankfurt', city_vars[12] == 'Frankfurt', city_vars[13] == 'Frankfurt', city_vars[14] == 'Frankfurt', city_vars[15] == 'Frankfurt']))  # Attend annual show in Frankfurt between day 12 and 16
    constraints.append(Or([city_vars[21] == 'Venice', city_vars[22] == 'Venice', city_vars[23] == 'Venice', city_vars[24] == 'Venice', city_vars[25] == 'Venice']))  # Attend wedding in Venice between day 22 and 26

    # Stay in each city for the required duration
    for city, duration in durations.items():
        constraints.append(Sum([If(city_vars[i] == city, 1, 0) for i in range(26)]) == duration)

    # Ensure that the trip plan is feasible (i.e., only take direct flights)
    for i in range(25):
        constraints.append(Or([And(city_vars[i] == from_city, city_vars[i+1] == to_city) for from_city, to_cities in direct_flights.items() for to_city in to_cities]))

    # Ensure that the trip plan is connected (i.e., no gaps in the trip plan)
    constraints.append(Distinct([city_vars[i] for i in range(26)]))

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