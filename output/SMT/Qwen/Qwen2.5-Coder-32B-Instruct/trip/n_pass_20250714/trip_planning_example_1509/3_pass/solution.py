from z3 import *

# Define the cities
cities = ["Paris", "Warsaw", "Krakow", "Tallinn", "Riga", "Copenhagen", "Helsinki", "Oslo", "Santorini", "Lyon"]

# Define the solver
solver = Solver()

# Define the variables for the start day of each city
city_start_vars = {city: Int(f"{city}_start_day") for city in cities}

# Define the duration for each city
durations = {
    "Paris": 5,
    "Warsaw": 2,
    "Krakow": 2,
    "Tallinn": 2,
    "Riga": 2,
    "Copenhagen": 5,
    "Helsinki": 5,
    "Oslo": 5,
    "Santorini": 2,
    "Lyon": 4
}

# Add constraints for each city
# Paris: 5 days, meeting friends between day 4 and day 8
solver.add(city_start_vars["Paris"] >= 1)
solver.add(city_start_vars["Paris"] <= 21)  # To allow 5 days within 25 days
for d in range(4, 9):
    solver.add(Or(city_start_vars["Paris"] > d, city_start_vars["Paris"] + durations["Paris"] - 1 < d))

# Warsaw: 2 days
solver.add(city_start_vars["Warsaw"] >= 1)
solver.add(city_start_vars["Warsaw"] <= 24)

# Krakow: 2 days, workshop between day 17 and day 18
solver.add(city_start_vars["Krakow"] >= 1)
solver.add(city_start_vars["Krakow"] <= 24)
solver.add(Or(city_start_vars["Krakow"] > 18, city_start_vars["Krakow"] + durations["Krakow"] - 1 < 17))

# Tallinn: 2 days
solver.add(city_start_vars["Tallinn"] >= 1)
solver.add(city_start_vars["Tallinn"] <= 24)

# Riga: 2 days, wedding between day 23 and day 24
solver.add(city_start_vars["Riga"] >= 1)
solver.add(city_start_vars["Riga"] <= 23)
solver.add(Or(city_start_vars["Riga"] > 24, city_start_vars["Riga"] + durations["Riga"] - 1 < 23))

# Copenhagen: 5 days
solver.add(city_start_vars["Copenhagen"] >= 1)
solver.add(city_start_vars["Copenhagen"] <= 21)

# Helsinki: 5 days, meeting friend between day 18 and day 22
solver.add(city_start_vars["Helsinki"] >= 1)
solver.add(city_start_vars["Helsinki"] <= 21)
for d in range(18, 23):
    solver.add(Or(city_start_vars["Helsinki"] > d, city_start_vars["Helsinki"] + durations["Helsinki"] - 1 < d))

# Oslo: 5 days
solver.add(city_start_vars["Oslo"] >= 1)
solver.add(city_start_vars["Oslo"] <= 21)

# Santorini: 2 days, visiting relatives between day 12 and day 13
solver.add(city_start_vars["Santorini"] >= 1)
solver.add(city_start_vars["Santorini"] <= 24)
solver.add(Or(city_start_vars["Santorini"] > 13, city_start_vars["Santorini"] + durations["Santorini"] - 1 < 12))

# Lyon: 4 days
solver.add(city_start_vars["Lyon"] >= 1)
solver.add(city_start_vars["Lyon"] <= 22)

# Ensure no overlap and correct sequence of visits
for i in range(len(cities)):
    for j in range(i + 1, len(cities)):
        city1, city2 = cities[i], cities[j]
        solver.add(Or(city_start_vars[city1] + durations[city1] <= city_start_vars[city2],
                       city_start_vars[city2] + durations[city2] <= city_start_vars[city1]))

# Ensure the total number of days is exactly 25
total_days = Sum([If(city_start_vars[city] + durations[city] <= 25, durations[city], 0) for city in cities])
solver.add(total_days == 25)

# Add constraints for direct flights
flight_constraints = [
    ("Warsaw", "Riga"), ("Warsaw", "Tallinn"), ("Copenhagen", "Helsinki"),
    ("Lyon", "Paris"), ("Copenhagen", "Warsaw"), ("Lyon", "Oslo"),
    ("Paris", "Oslo"), ("Paris", "Riga"), ("Krakow", "Helsinki"),
    ("Paris", "Tallinn"), ("Oslo", "Riga"), ("Krakow", "Warsaw"),
    ("Paris", "Helsinki"), ("Copenhagen", "Santorini"), ("Helsinki", "Warsaw"),
    ("Helsinki", "Riga"), ("Copenhagen", "Krakow"), ("Copenhagen", "Riga"),
    ("Paris", "Krakow"), ("Copenhagen", "Oslo"), ("Oslo", "Tallinn"),
    ("Oslo", "Helsinki"), ("Copenhagen", "Tallinn"), ("Oslo", "Krakow"),
    ("Riga", "Tallinn"), ("Helsinki", "Tallinn"), ("Paris", "Copenhagen"),
    ("Paris", "Warsaw"), ("Santorini", "Oslo"), ("Oslo", "Warsaw")
]

# Ensure flights are possible
for (city1, city2) in flight_constraints:
    solver.add(Or(city_start_vars[city1] + durations[city1] <= city_start_vars[city2],
                   city_start_vars[city2] + durations[city2] <= city_start_vars[city1]))

# Check if the solution is satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city in cities:
        start_day = model.evaluate(city_start_vars[city]).as_long()
        end_day = start_day + durations[city] - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        if start_day != end_day:
            itinerary.append({"day_range": f"Day {end_day}", "place": city})

    # Sort the itinerary by day
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

    # Print the itinerary in JSON format
    print({"itinerary": itinerary})
else:
    print("No solution found")