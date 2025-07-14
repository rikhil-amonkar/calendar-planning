from z3 import *

# Define the solver
solver = Solver()

# Define the number of days
num_days = 16

# Define the cities
cities = ["Mykonos", "Reykjavik", "Dublin", "London", "Helsinki", "Hamburg"]

# Define the variables for the start day in each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Define the constraints for the number of days in each city
days_in_city = {
    "Mykonos": 3,
    "Reykjavik": 2,
    "Dublin": 5,
    "London": 5,
    "Helsinki": 4,
    "Hamburg": 2
}

# Add constraints for the number of days in each city
for city, days in days_in_city.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + days <= num_days)

# Constraints for specific events
# Dublin show from day 2 to day 6
solver.add(start_days["Dublin"] <= 2)
solver.add(start_days["Dublin"] + days_in_city["Dublin"] >= 7)

# Wedding in Reykjavik on day 9 and day 10
solver.add(start_days["Reykjavik"] <= 9)
solver.add(start_days["Reykjavik"] + days_in_city["Reykjavik"] >= 11)

# Meeting friends in Hamburg on day 1 and day 2
solver.add(start_days["Hamburg"] == 1)

# Define the direct flights
direct_flights = [
    ("Dublin", "London"),
    ("Hamburg", "Dublin"),
    ("Helsinki", "Reykjavik"),
    ("Hamburg", "London"),
    ("Dublin", "Helsinki"),
    ("Reykjavik", "London"),
    ("London", "Mykonos"),
    ("Dublin", "Reykjavik"),
    ("Hamburg", "Helsinki"),
    ("Helsinki", "London")
]

# Add constraints for direct flights
for i in range(1, num_days):
    current_city = Int(f"current_city_day_{i}")
    next_city = Int(f"next_city_day_{i}")
    
    # Each day must be in one of the cities
    solver.add(Or([current_city == j for j in range(len(cities))]))
    
    # Define the city for each day
    city_vars = [If(current_city == j, cities[j], "") for j in range(len(cities))]
    current_city_name = Concat(city_vars)
    
    # Define the next city for each day
    city_vars_next = [If(next_city == j, cities[j], "") for j in range(len(cities))]
    next_city_name = Concat(city_vars_next)
    
    # Ensure that the transition is valid
    solver.add(Or([And(current_city_name == c1, next_city_name == c2) for c1, c2 in direct_flights] + [current_city_name == next_city_name]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, num_days + 1):
        for city in cities:
            if model.evaluate(start_days[city]) <= day and model.evaluate(start_days[city]) + days_in_city[city] > day:
                itinerary.append({"day_range": f"Day {day}", "place": city})
                break
    
    # Adjust for flight days
    adjusted_itinerary = []
    for i in range(len(itinerary)):
        if i > 0 and itinerary[i]["place"] != itinerary[i-1]["place"]:
            adjusted_itinerary.append({"day_range": itinerary[i-1]["day_range"], "place": itinerary[i-1]["place"]})
            adjusted_itinerary.append({"day_range": itinerary[i]["day_range"], "place": itinerary[i]["place"]})
        else:
            adjusted_itinerary.append(itinerary[i])
    
    # Merge consecutive days in the same city
    final_itinerary = []
    current_entry = None
    for entry in adjusted_itinerary:
        if current_entry and current_entry["place"] == entry["place"] and int(current_entry["day_range"].split()[1]) + 1 == int(entry["day_range"].split()[1]):
            current_entry["day_range"] = f"Day {current_entry['day_range'].split()[1]}-{entry['day_range'].split()[1]}"
        else:
            if current_entry:
                final_itinerary.append(current_entry)
            current_entry = entry
    if current_entry:
        final_itinerary.append(current_entry)
    
    print({"itinerary": final_itinerary})
else:
    print("No solution found")