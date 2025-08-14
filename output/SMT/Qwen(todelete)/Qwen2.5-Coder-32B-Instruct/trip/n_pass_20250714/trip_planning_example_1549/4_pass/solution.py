from z3 import *

# Define the cities and their respective stay durations
cities = {
    "Prague": 5,
    "Tallinn": 3,
    "Warsaw": 2,
    "Porto": 3,
    "Naples": 5,
    "Milan": 3,
    "Lisbon": 5,
    "Santorini": 5,
    "Riga": 4,
    "Stockholm": 2
}

# Define the special days for each city
special_days = {
    "Tallinn": (18, 20),
    "Milan": (24, 26),
    "Riga": (5, 8)
}

# Define the direct flights between cities
flights = [
    ("Riga", "Prague"), ("Stockholm", "Milan"), ("Riga", "Milan"),
    ("Lisbon", "Stockholm"), ("Stockholm", "Santorini"), ("Naples", "Warsaw"),
    ("Lisbon", "Warsaw"), ("Naples", "Milan"), ("Lisbon", "Naples"),
    ("Riga", "Tallinn"), ("Tallinn", "Prague"), ("Stockholm", "Warsaw"),
    ("Riga", "Warsaw"), ("Lisbon", "Riga"), ("Riga", "Stockholm"),
    ("Lisbon", "Porto"), ("Lisbon", "Prague"), ("Milan", "Porto"),
    ("Prague", "Milan"), ("Lisbon", "Milan"), ("Warsaw", "Porto"),
    ("Warsaw", "Tallinn"), ("Santorini", "Milan"), ("Stockholm", "Prague"),
    ("Stockholm", "Tallinn"), ("Warsaw", "Milan"), ("Santorini", "Naples"),
    ("Warsaw", "Prague")
]

# Create a solver instance
solver = Solver()

# Create variables for the start day of each city
start_vars = {city: Int(f"start_{city}") for city in cities}

# Add constraints for each city
for city, duration in cities.items():
    start = start_vars[city]
    end = start + duration - 1
    solver.add(start >= 1)
    solver.add(end <= 28)
    if city in special_days:
        start_special, end_special = special_days[city]
        solver.add(Or(end < start_special, start > end_special))

# Ensure the total duration is exactly 28 days
# We need to ensure that the itinerary covers all 28 days without gaps or overlaps
# and that transitions are valid

# Create a list of all days
days = [Bool(f"day_{d}") for d in range(1, 29)]

# Add constraints for each day to be covered by exactly one city or transition
for d in range(1, 29):
    day_constraints = []
    for city, duration in cities.items():
        start = start_vars[city]
        end = start + duration - 1
        day_in_city = And(d >= start, d <= end)
        day_constraints.append(day_in_city)
    # Add constraints for transitions
    for (city1, city2) in flights:
        end1 = start_vars[city1] + cities[city1] - 1
        start2 = start_vars[city2]
        transition_day = And(d == end1 + 1, d == start2)
        day_constraints.append(transition_day)
    solver.add(Or(*day_constraints))

# Ensure the itinerary covers exactly 28 days
# We need to add constraints to ensure there are no gaps or overlaps
# and that the total duration is exactly 28 days

# Add constraints to ensure no gaps or overlaps
for city1, duration1 in cities.items():
    end1 = start_vars[city1] + duration1 - 1
    for city2, duration2 in cities.items():
        if city1 != city2:
            start2 = start_vars[city2]
            end2 = start_vars[city2] + duration2 - 1
            solver.add(Or(end1 < start2, end2 < start1))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city, start_var in start_vars.items():
        start_day = model[start_var].as_long()
        end_day = start_day + cities[city] - 1
        if start_day == end_day:
            itinerary.append({"day_range": f"Day {start_day}", "place": city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
            if start_day + cities[city] - 2 >= start_day:
                itinerary.append({"day_range": f"Day {start_day + cities[city] - 1}", "place": city})

    # Sort the itinerary by day
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

    # Handle flight days
    for i in range(len(itinerary) - 1):
        end_day = int(itinerary[i]["day_range"].split()[1].split('-')[-1])
        start_day_next = int(itinerary[i + 1]["day_range"].split()[1].split('-')[0])
        if end_day + 1 == start_day_next:
            city_from = itinerary[i]["place"]
            city_to = itinerary[i + 1]["place"]
            if (city_from, city_to) in flights or (city_to, city_from) in flights:
                itinerary.insert(i + 1, {"day_range": f"Day {end_day + 1}", "place": city_to})

    print({"itinerary": itinerary})
else:
    print("No solution found")