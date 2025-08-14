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

# Create a variable for each day to represent the city
city_vars = [Int(f"city_day_{i}") for i in range(num_days)]

# Map city indices
city_indices = {city: i for i, city in enumerate(cities)}

# Add constraints for each day
for day in range(num_days):
    # Each day must be in one of the cities
    solver.add(Or([city_vars[day] == city_indices[city] for city in cities]))
    
    # Ensure that the transition is valid
    if day < num_days - 1:
        solver.add(Or(
            [And(city_vars[day] == city_indices[c1], city_vars[day + 1] == city_indices[c2]) for c1, c2 in direct_flights] +
            [city_vars[day] == city_vars[day + 1]]
        ))

# Ensure each city's start and end days match the days_in_city constraint
for city, days in days_in_city.items():
    start = start_days[city]
    end = start + days - 1
    for day in range(num_days):
        city_var = city_vars[day]
        solver.add(Implies(city_var == city_indices[city], And(start <= day + 1, day + 1 <= end)))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(num_days):
        city_index = model.eval(city_vars[day]).as_long()
        city_name = cities[city_index]
        itinerary.append({"day_range": f"Day {day + 1}", "place": city_name})
    
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
        if current_entry and current_entry["place"] == entry["place"]:
            current_day = int(entry["day_range"].split()[1])
            current_end_day = int(current_entry["day_range"].split('-')[-1]) if '-' in current_entry["day_range"] else int(current_entry["day_range"].split()[1])
            if current_day == current_end_day + 1:
                current_entry["day_range"] = f"Day {current_entry['day_range'].split()[1]}-{current_day}"
            else:
                final_itinerary.append(current_entry)
                current_entry = entry
        else:
            if current_entry:
                final_itinerary.append(current_entry)
            current_entry = entry
    if current_entry:
        final_itinerary.append(current_entry)
    
    print({"itinerary": final_itinerary})
else:
    print("No solution found")