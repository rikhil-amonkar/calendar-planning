from z3 import *

# Define the cities and their stay durations
cities = ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest']
durations = {'Riga': 2, 'Frankfurt': 3, 'Amsterdam': 2, 'Vilnius': 5, 'London': 2, 'Stockholm': 3, 'Bucharest': 4}

# Define the direct flights between cities
direct_flights = {
    'London': ['Amsterdam'],
    'Vilnius': ['Frankfurt'],
    'Riga': ['Vilnius'],
    'Riga': ['Stockholm'],
    'London': ['Bucharest'],
    'Amsterdam': ['Stockholm'],
    'Amsterdam': ['Frankfurt'],
    'Frankfurt': ['Stockholm'],
    'Bucharest': ['Riga'],
    'Amsterdam': ['Riga'],
    'Amsterdam': ['Bucharest'],
    'Riga': ['Frankfurt'],
    'Bucharest': ['Frankfurt'],
    'London': ['Frankfurt'],
    'London': ['Stockholm'],
    'Amsterdam': ['Vilnius']
}

# Define the constraints
def define_constraints():
    # Define the variables
    city_vars = [Int(f'city_{i}') for i in range(15)]
    for var in city_vars:
        var.domain(cities)

    # Define the constraints
    constraints = []
    constraints.append(Or([city_vars[1] == 'Amsterdam', city_vars[2] == 'Amsterdam']))  # Meet a friend in Amsterdam between day 2 and 3
    constraints.append(Or([city_vars[6] == 'Vilnius', city_vars[7] == 'Vilnius', city_vars[8] == 'Vilnius', city_vars[9] == 'Vilnius', city_vars[10] == 'Vilnius']))  # Attend workshop in Vilnius between day 7 and 11
    constraints.append(Or([city_vars[12] == 'Stockholm', city_vars[13] == 'Stockholm', city_vars[14] == 'Stockholm']))  # Attend wedding in Stockholm between day 13 and 15

    # Stay in each city for the required duration
    for city, duration in durations.items():
        constraints.append(Sum([If(city_vars[i] == city, 1, 0) for i in range(15)]) == duration)

    # Ensure that the trip plan is feasible (i.e., only take direct flights)
    for i in range(14):
        constraints.append(Or([And(city_vars[i] == from_city, city_vars[i+1] == to_city) for from_city, to_cities in direct_flights.items() for to_city in to_cities]))

    # Ensure that the trip plan is connected (i.e., no gaps in the trip plan)
    constraints.append(Distinct([city_vars[i] for i in range(15)]))

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