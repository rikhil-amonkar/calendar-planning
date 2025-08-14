from z3 import *

# Define the solver
solver = Solver()

# Define the variables
days = range(1, 26)
cities = ["Paris", "Warsaw", "Krakow", "Tallinn", "Riga", "Copenhagen", "Helsinki", "Oslo", "Santorini", "Lyon"]
city_vars = {city: Int(f"{city}_day") for city in cities}

# Add constraints for each city
# Paris: 5 days, meeting friends between day 4 and day 8
solver.add(city_vars["Paris"] >= 1)
solver.add(city_vars["Paris"] <= 21)  # To allow 5 days within 25 days
for d in range(4, 9):
    solver.add(Or(city_vars["Paris"] > d, city_vars["Paris"] + 4 < d))

# Warsaw: 2 days
solver.add(city_vars["Warsaw"] >= 1)
solver.add(city_vars["Warsaw"] <= 24)

# Krakow: 2 days, workshop between day 17 and day 18
solver.add(city_vars["Krakow"] >= 1)
solver.add(city_vars["Krakow"] <= 24)
solver.add(Or(city_vars["Krakow"] > 18, city_vars["Krakow"] + 1 < 17))

# Tallinn: 2 days
solver.add(city_vars["Tallinn"] >= 1)
solver.add(city_vars["Tallinn"] <= 24)

# Riga: 2 days, wedding between day 23 and day 24
solver.add(city_vars["Riga"] >= 1)
solver.add(city_vars["Riga"] <= 23)
solver.add(Or(city_vars["Riga"] > 24, city_vars["Riga"] + 1 < 23))

# Copenhagen: 5 days
solver.add(city_vars["Copenhagen"] >= 1)
solver.add(city_vars["Copenhagen"] <= 21)

# Helsinki: 5 days, meeting friend between day 18 and day 22
solver.add(city_vars["Helsinki"] >= 1)
solver.add(city_vars["Helsinki"] <= 21)
for d in range(18, 23):
    solver.add(Or(city_vars["Helsinki"] > d, city_vars["Helsinki"] + 4 < d))

# Oslo: 5 days
solver.add(city_vars["Oslo"] >= 1)
solver.add(city_vars["Oslo"] <= 21)

# Santorini: 2 days, visiting relatives between day 12 and day 13
solver.add(city_vars["Santorini"] >= 1)
solver.add(city_vars["Santorini"] <= 24)
solver.add(Or(city_vars["Santorini"] > 13, city_vars["Santorini"] + 1 < 12))

# Lyon: 4 days
solver.add(city_vars["Lyon"] >= 1)
solver.add(city_vars["Lyon"] <= 22)

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

for (city1, city2) in flight_constraints:
    for d in days:
        solver.add(Or(city_vars[city1] != d - 1, city_vars[city2] == d))
        solver.add(Or(city_vars[city2] != d - 1, city_vars[city1] == d))

# Check if the solution is satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city in cities:
        start_day = model.evaluate(city_vars[city]).as_long()
        if city == "Paris":
            itinerary.append({"day_range": f"Day {start_day}-{start_day + 4}", "place": city})
            itinerary.append({"day_range": f"Day {start_day + 4}", "place": city})
        elif city == "Warsaw":
            itinerary.append({"day_range": f"Day {start_day}-{start_day + 1}", "place": city})
            itinerary.append({"day_range": f"Day {start_day + 1}", "place": city})
        elif city == "Krakow":
            itinerary.append({"day_range": f"Day {start_day}-{start_day + 1}", "place": city})
            itinerary.append({"day_range": f"Day {start_day + 1}", "place": city})
        elif city == "Tallinn":
            itinerary.append({"day_range": f"Day {start_day}-{start_day + 1}", "place": city})
            itinerary.append({"day_range": f"Day {start_day + 1}", "place": city})
        elif city == "Riga":
            itinerary.append({"day_range": f"Day {start_day}-{start_day + 1}", "place": city})
            itinerary.append({"day_range": f"Day {start_day + 1}", "place": city})
        elif city == "Copenhagen":
            itinerary.append({"day_range": f"Day {start_day}-{start_day + 4}", "place": city})
            itinerary.append({"day_range": f"Day {start_day + 4}", "place": city})
        elif city == "Helsinki":
            itinerary.append({"day_range": f"Day {start_day}-{start_day + 4}", "place": city})
            itinerary.append({"day_range": f"Day {start_day + 4}", "place": city})
        elif city == "Oslo":
            itinerary.append({"day_range": f"Day {start_day}-{start_day + 4}", "place": city})
            itinerary.append({"day_range": f"Day {start_day + 4}", "place": city})
        elif city == "Santorini":
            itinerary.append({"day_range": f"Day {start_day}-{start_day + 1}", "place": city})
            itinerary.append({"day_range": f"Day {start_day + 1}", "place": city})
        elif city == "Lyon":
            itinerary.append({"day_range": f"Day {start_day}-{start_day + 3}", "place": city})
            itinerary.append({"day_range": f"Day {start_day + 3}", "place": city})

    # Sort the itinerary by day
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

    # Print the itinerary in JSON format
    print({"itinerary": itinerary})
else:
    print("No solution found")