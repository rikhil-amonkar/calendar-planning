from z3 import *
import json

# --- Constants and helper definitions ---
days = 7
# We encode the cities as integers:
# 0 = Riga, 1 = Amsterdam, 2 = Mykonos
Riga = 0
Amsterdam = 1
Mykonos = 2
city_names = ["Riga", "Amsterdam", "Mykonos"]

# --- Create the Z3 model ---
solver = Solver()

# Create a variable for the “city” on each day.
# Note: our interpretation is that if there is no flight on a day then the traveler is only in that city,
# but if a flight occurs then that day counts for the departing city (from the previous day)
# and for the arriving city.
city = [Int(f"city_{i}") for i in range(days)]
for i in range(days):
    solver.add(Or(city[i] == Riga, city[i] == Amsterdam, city[i] == Mykonos))

# Constraint: The plan “visits relatives in Riga between day 1 and day 2.”
# We force day 1 to be in Riga.
solver.add(city[0] == Riga)

# Flight constraint:
# If the city changes from day i-1 to day i then a flight occurred and it must be between two cities that have a direct flight.
for i in range(1, days):
    # A flight occurs on day i if city[i] != city[i-1].
    flight_occurs = city[i] != city[i-1]
    allowed_flight = Or(
        And(city[i-1] == Riga, city[i] == Amsterdam),
        And(city[i-1] == Amsterdam, city[i] == Riga),
        And(city[i-1] == Amsterdam, city[i] == Mykonos),
        And(city[i-1] == Mykonos, city[i] == Amsterdam)
    )
    solver.add(Implies(flight_occurs, allowed_flight))
    
# Counting each day’s contribution:
# The idea is that day 0 (the initial day) counts only for its city.
# For each subsequent day i (i>=1):
# - If there is no flight, then only city[i] gets 1 day.
# - If a flight occurs (city[i] != city[i-1]), then day i counts as 1 day
#   for the previous city (the “departure”) and 1 day for the current city (the “arrival”).
def day_count_expr(city_constant):
    expr = If(city[0] == city_constant, 1, 0)
    for i in range(1, days):
        expr += If(city[i] == city[i-1],
                   # No flight: add only 1 if the city on day i equals the constant.
                   If(city[i] == city_constant, 1, 0),
                   # Flight: add 1 for the previous city (if it is the constant)
                   #        and 1 for the current city (if it is the constant)
                   (If(city[i-1] == city_constant, 1, 0) + If(city[i] == city_constant, 1, 0))
                  )
    return expr

# Add the requirements on the total days spent in each city.
solver.add(day_count_expr(Riga) == 2)       # Must spend 2 days in Riga.
solver.add(day_count_expr(Amsterdam) == 2)    # Must spend 2 days in Amsterdam.
solver.add(day_count_expr(Mykonos) == 5)        # Must spend 5 days in Mykonos.

# --- Solve and extract a model ---
if solver.check() == sat:
    model = solver.model()
    city_solution = [model.evaluate(city[i]).as_long() for i in range(days)]
    
    # Build the itinerary.
    # For day 1 (i==0) there is no flight.
    # For any day i>=1, if city[i] != city[i-1] then the traveler took a flight on that day,
    # so that day counts for both cities.
    itinerary = []
    for i in range(days):
        if i == 0:
            itinerary.append({"day": i+1, "places": [city_names[city_solution[i]]]})
        else:
            if city_solution[i] == city_solution[i-1]:
                itinerary.append({"day": i+1, "places": [city_names[city_solution[i]]]})
            else:
                itinerary.append({"day": i+1, "places": [city_names[city_solution[i-1]], city_names[city_solution[i]]]})
                
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")