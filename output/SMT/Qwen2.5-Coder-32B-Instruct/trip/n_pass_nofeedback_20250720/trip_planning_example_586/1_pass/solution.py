from z3 import *

# Define the solver
solver = Solver()

# Define the number of days
total_days = 12

# Define the cities and their required stay durations
cities = {
    "Frankfurt": 3,
    "Naples": 4,
    "Helsinki": 4,
    "Lyon": 3,
    "Prague": 2
}

# Define the direct flight connections
flights = {
    ("Prague", "Lyon"),
    ("Prague", "Frankfurt"),
    ("Frankfurt", "Lyon"),
    ("Helsinki", "Naples"),
    ("Helsinki", "Frankfurt"),
    ("Naples", "Frankfurt"),
    ("Prague", "Helsinki")
}

# Create a list of variables for each day and city
# day_city[i][j] is true if the person is in city j on day i
day_city = [[Bool(f"day_{i}_city_{j}") for j in cities] for i in range(total_days)]

# Create a mapping from city names to indices
city_indices = {city: idx for idx, city in enumerate(cities)}

# Add constraints for the required stay durations
for city, days in cities.items():
    city_idx = city_indices[city]
    # The person must be in the city for the required number of days
    solver.add(Sum([If(day_city[i][city_idx], 1, 0) for i in range(total_days)]) == days)

# Add constraints for the specific events
# Workshop in Prague between day 1 and day 2
solver.add(Or(day_city[0][city_indices["Prague"]], day_city[1][city_indices["Prague"]]))

# Annual show in Helsinki from day 2 to day 5
for day in range(1, 5):
    solver.add(day_city[day][city_indices["Helsinki"]])

# Add constraints for direct flights
for i in range(total_days - 1):
    for city1, city2 in flights:
        city1_idx = city_indices[city1]
        city2_idx = city_indices[city2]
        # If the person is in city1 on day i and city2 on day i+1, they must have flown directly
        solver.add(Implies(And(day_city[i][city1_idx], day_city[i + 1][city2_idx]), Or(
            And(day_city[i][city2_idx], day_city[i + 1][city2_idx]),  # Stay in city2
            And(day_city[i][city1_idx], day_city[i + 1][city1_idx])   # Stay in city1
        )))
        # If the person is in city2 on day i and city1 on day i+1, they must have flown directly
        solver.add(Implies(And(day_city[i][city2_idx], day_city[i + 1][city1_idx]), Or(
            And(day_city[i][city1_idx], day_city[i + 1][city1_idx]),  # Stay in city1
            And(day_city[i][city2_idx], day_city[i + 1][city2_idx])   # Stay in city2
        )))

# Add constraints to ensure the person is in exactly one city per day
for i in range(total_days):
    solver.add(Exactly(1, [day_city[i][j] for j in range(len(cities))]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = {}
    for i in range(total_days):
        for j, city in enumerate(cities):
            if model.evaluate(day_city[i][j]):
                if city not in itinerary:
                    itinerary[city] = []
                itinerary[city].append(i + 1)
    # Convert the itinerary to the required format
    formatted_itinerary = [{"day": day, "city": city} for city, days in itinerary.items() for day in days]
    formatted_itinerary.sort(key=lambda x: x["day"])
    result = {"itinerary": formatted_itinerary}
    print(result)
else:
    print("No solution found")