from z3 import *

# Define the number of days and cities
days = range(1, 13)
cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]

# Create a Z3 solver instance
solver = Solver()

# Define variables for the day each city starts
start_days = {city: Int(f"start_{city}") for city in cities}

# Constraints for the number of days in each city
constraints = [
    start_days["Split"] + 2 <= 13,
    start_days["Helsinki"] + 2 <= 13,
    start_days["Reykjavik"] + 3 <= 13,
    start_days["Vilnius"] + 3 <= 13,
    start_days["Geneva"] + 6 <= 13
]

# Constraints for specific days in Reykjavik and Vilnius
constraints.append(start_days["Reykjavik"] <= 10)
constraints.append(start_days["Reykjavik"] + 2 >= 8)  # To ensure at least one day between 10 and 12
constraints.append(start_days["Vilnius"] <= 7)
constraints.append(start_days["Vilnius"] + 2 >= 5)   # To ensure at least one day between 7 and 9

# Constraints for direct flights
# We need to ensure that transitions between cities are valid and via direct flights
flight_constraints = []

# Direct flights: Split <-> Helsinki, Geneva <-> Split, Geneva <-> Helsinki, Helsinki <-> Reykjavik, Vilnius <-> Helsinki, Split <-> Vilnius
flight_constraints.append(Or(
    And(start_days["Split"] + 2 == start_days["Helsinki"], start_days["Helsinki"] - start_days["Split"] == 2),
    And(start_days["Helsinki"] + 2 == start_days["Split"], start_days["Split"] - start_days["Helsinki"] == 2)
))

flight_constraints.append(Or(
    And(start_days["Geneva"] + 6 == start_days["Split"], start_days["Split"] - start_days["Geneva"] == 6),
    And(start_days["Split"] + 2 == start_days["Geneva"], start_days["Geneva"] - start_days["Split"] == 2)
))

flight_constraints.append(Or(
    And(start_days["Geneva"] + 6 == start_days["Helsinki"], start_days["Helsinki"] - start_days["Geneva"] == 6),
    And(start_days["Helsinki"] + 2 == start_days["Geneva"], start_days["Geneva"] - start_days["Helsinki"] == 2)
))

flight_constraints.append(Or(
    And(start_days["Helsinki"] + 2 == start_days["Reykjavik"], start_days["Reykjavik"] - start_days["Helsinki"] == 2),
    And(start_days["Reykjavik"] + 3 == start_days["Helsinki"], start_days["Helsinki"] - start_days["Reykjavik"] == 3)
))

flight_constraints.append(Or(
    And(start_days["Vilnius"] + 3 == start_days["Helsinki"], start_days["Helsinki"] - start_days["Vilnius"] == 3),
    And(start_days["Helsinki"] + 2 == start_days["Vilnius"], start_days["Vilnius"] - start_days["Helsinki"] == 2)
))

flight_constraints.append(Or(
    And(start_days["Split"] + 2 == start_days["Vilnius"], start_days["Vilnius"] - start_days["Split"] == 2),
    And(start_days["Vilnius"] + 3 == start_days["Split"], start_days["Split"] - start_days["Vilnius"] == 3)
))

# Add all constraints to the solver
solver.add(constraints)
solver.add(flight_constraints)

# Check if the constraints can be satisfied
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city in cities:
        start_day = model[start_days[city]].as_long()
        if city == "Split":
            itinerary.append({"day_range": f"Day {start_day}-{start_day+1}", "place": "Split"})
            itinerary.append({"day_range": f"Day {start_day+2}", "place": "Split"})
        elif city == "Helsinki":
            itinerary.append({"day_range": f"Day {start_day}-{start_day+1}", "place": "Helsinki"})
            itinerary.append({"day_range": f"Day {start_day+2}", "place": "Helsinki"})
        elif city == "Reykjavik":
            itinerary.append({"day_range": f"Day {start_day}-{start_day+2}", "place": "Reykjavik"})
        elif city == "Vilnius":
            itinerary.append({"day_range": f"Day {start_day}-{start_day+2}", "place": "Vilnius"})
        elif city == "Geneva":
            itinerary.append({"day_range": f"Day {start_day}-{start_day+5}", "place": "Geneva"})
    
    # Sort the itinerary by day_range
    itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split(' ')[1]))
    
    # Adjust for flight days
    final_itinerary = []
    i = 0
    while i < len(itinerary):
        current = itinerary[i]
        next_day = int(current['day_range'].split('-')[-1].split(' ')[1]) + 1
        if i + 1 < len(itinerary) and int(itinerary[i + 1]['day_range'].split('-')[0].split(' ')[1]) == next_day:
            final_itinerary.append(current)
            final_itinerary.append({"day_range": f"Day {next_day}", "place": itinerary[i + 1]['place']})
            final_itinerary.append(itinerary[i + 1])
            i += 2
        else:
            final_itinerary.append(current)
            i += 1
    
    print({"itinerary": final_itinerary})
else:
    print("No solution found")