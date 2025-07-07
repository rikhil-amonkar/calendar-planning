from z3 import *

# Define the number of days
num_days = 21

# Define the cities
cities = ["Reykjavik", "Oslo", "Stuttgart", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]

# Create a dictionary to store the variables for each city and day
city_vars = {city: [Bool(f"{city}_day_{i}") for i in range(1, num_days + 1)] for city in cities}

# Create a solver instance
solver = Solver()

# Add constraints for the required stays in each city
required_stays = {
    "Oslo": 5,
    "Stuttgart": 5,
    "Reykjavik": 2,
    "Split": 3,
    "Geneva": 2,
    "Porto": 3,
    "Tallinn": 5,
    "Stockholm": 3
}

for city, days in required_stays.items():
    # Ensure the sum of days spent in each city is equal to the required stay
    solver.add(Sum([If(city_vars[city][i], 1, 0) for i in range(num_days)]) == days)

# Add constraints for specific days in specific cities
solver.add(city_vars["Reykjavik"][0])  # Day 1 in Reykjavik
solver.add(city_vars["Reykjavik"][1])  # Day 2 in Reykjavik
solver.add(city_vars["Porto"][18])   # Day 19 in Porto
solver.add(city_vars["Porto"][19])   # Day 20 in Porto
solver.add(city_vars["Porto"][20])   # Day 21 in Porto
solver.add(city_vars["Stockholm"][1])  # Day 2 in Stockholm
solver.add(city_vars["Stockholm"][2])  # Day 3 in Stockholm
solver.add(city_vars["Stockholm"][3])  # Day 4 in Stockholm

# Add constraints for direct flights
direct_flights = [
    ("Reykjavik", "Stuttgart"), ("Stockholm", "Reykjavik"), ("Tallinn", "Reykjavik"),
    ("Stockholm", "Oslo"), ("Stuttgart", "Porto"), ("Oslo", "Split"), ("Stockholm", "Stuttgart"),
    ("Reykjavik", "Oslo"), ("Oslo", "Geneva"), ("Stockholm", "Split"), ("Reykjavik", "Stockholm"),
    ("Split", "Stuttgart"), ("Tallinn", "Oslo"), ("Stockholm", "Geneva"), ("Oslo", "Porto"),
    ("Geneva", "Porto"), ("Geneva", "Split")
]

# Ensure that if a city is visited on a day, it can only be visited through a direct flight from another city or itself
for day in range(num_days):
    for city in cities:
        # If the city is visited on this day, ensure it's either the first day or reachable from another city
        if day > 0:
            reachable = Or(city_vars[city][day - 1])  # Stay in the same city
            for prev_city, next_city in direct_flights:
                if next_city == city:
                    reachable = Or(reachable, city_vars[prev_city][day - 1])
            solver.add(Implies(city_vars[city][day], reachable))

# Ensure that each day is accounted for exactly once
for day in range(num_days):
    solver.add(Or([city_vars[city][day] for city in cities]))

# Ensure no overlap between different cities on the same day
for day in range(num_days):
    for i in range(len(cities)):
        for j in range(i + 1, len(cities)):
            solver.add(Not(And(city_vars[cities[i]][day], city_vars[cities[j]][day])))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    current_day = 1
    while current_day <= num_days:
        for city in cities:
            if model.evaluate(city_vars[city][current_day - 1]):
                start_day = current_day
                while current_day <= num_days and model.evaluate(city_vars[city][current_day - 1]):
                    current_day += 1
                end_day = current_day - 1
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                break
    print({"itinerary": itinerary})
else:
    print("No solution found")