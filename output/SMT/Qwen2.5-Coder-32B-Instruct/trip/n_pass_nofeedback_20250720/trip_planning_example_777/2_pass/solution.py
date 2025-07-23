from z3 import *
import json

# Define the cities and their required stay durations
cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
stay_durations = {'Dublin': 5, 'Helsinki': 3, 'Riga': 3, 'Reykjavik': 2, 'Vienna': 2, 'Tallinn': 5}

# Define the direct flight connections
connections = {
    'Helsinki': ['Riga', 'Dublin', 'Tallinn', 'Vienna'],
    'Riga': ['Helsinki', 'Tallinn', 'Dublin', 'Vienna'],
    'Tallinn': ['Helsinki', 'Riga', 'Dublin'],
    'Vienna': ['Helsinki', 'Riga', 'Reykjavik', 'Dublin'],
    'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
    'Dublin': ['Helsinki', 'Riga', 'Tallinn', 'Vienna', 'Reykjavik']
}

# Create a solver instance
solver = Solver()

# Define the start day for each city as a Z3 integer variable
start_days = {city: Int(f'start_{city}') for city in cities}

# Add constraints for the stay durations
for city, duration in stay_durations.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 15)

# Add constraints for the specific events
# Meet friends in Helsinki between day 3 and day 5
solver.add(Or(And(start_days['Helsinki'] + 2 >= 3, start_days['Helsinki'] + 2 <= 5),
              And(start_days['Helsinki'] + 1 >= 3, start_days['Helsinki'] + 1 <= 5),
              And(start_days['Helsinki'] >= 3, start_days['Helsinki'] <= 5)))

# Attend annual show in Vienna between day 2 and day 3
solver.add(Or(And(start_days['Vienna'] + 1 >= 2, start_days['Vienna'] + 1 <= 3),
              And(start_days['Vienna'] >= 2, start_days['Vienna'] <= 3)))

# Attend wedding in Tallinn between day 7 and day 11
solver.add(Or(And(start_days['Tallinn'] + 4 >= 7, start_days['Tallinn'] + 4 <= 11),
              And(start_days['Tallinn'] + 3 >= 7, start_days['Tallinn'] + 3 <= 11),
              And(start_days['Tallinn'] + 2 >= 7, start_days['Tallinn'] + 2 <= 11),
              And(start_days['Tallinn'] + 1 >= 7, start_days['Tallinn'] + 1 <= 11),
              And(start_days['Tallinn'] >= 7, start_days['Tallinn'] <= 11)))

# Add constraints for the transitions between cities
for city, connected_cities in connections.items():
    for connected_city in connected_cities:
        # If you start in city A and end in city B, the start day of B must be the end day of A + 1
        solver.add(Implies(start_days[city] + stay_durations[city] <= start_days[connected_city],
                           start_days[city] + stay_durations[city] == start_days[connected_city]))

# Ensure that the total duration is 15 days
total_days = Sum([stay_durations[city] for city in cities]) - Sum([If(start_days[city] + stay_durations[city] <= start_days[next_city], 1, 0) for city in cities for next_city in connections[city]])
solver.add(total_days == 15)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city in cities:
        start_day = model[start_days[city]].as_long()
        end_day = start_day + stay_durations[city] - 1
        for day in range(start_day, end_day + 1):
            itinerary.append({'day': day, 'place': city})
    itinerary.sort(key=lambda x: x['day'])
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found")