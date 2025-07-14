from z3 import *

# Define the cities
cities = ["Hamburg", "Zurich", "Helsinki", "Bucharest", "Split"]

# Define the variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Define the stay durations
stay_durations = {"Hamburg": 2, "Zurich": 3, "Helsinki": 2, "Bucharest": 2, "Split": 7}

# Create a solver instance
solver = Solver()

# Total stay is 12 days
total_days = 12

# Ensure the itinerary covers exactly 12 days
solver.add(start_days["Split"] + stay_durations["Split"] == total_days + 1)

# Specific constraints for days in cities
# Attend wedding between day 1 and day 3 in Zurich
solver.add(start_days["Zurich"] + 2 >= 1)
solver.add(start_days["Zurich"] <= 1)

# Attend conference between day 4 and day 10 in Split
solver.add(start_days["Split"] + 3 >= 4)
solver.add(start_days["Split"] <= 4)

# Flight constraints
# Ensure that flights are possible and direct flights are taken
solver.add(Or(
    And(start_days["Hamburg"] + stay_durations["Hamburg"] == start_days["Zurich"]),
    And(start_days["Zurich"] + stay_durations["Zurich"] == start_days["Hamburg"])
))
solver.add(Or(
    And(start_days["Zurich"] + stay_durations["Zurich"] == start_days["Helsinki"]),
    And(start_days["Helsinki"] + stay_durations["Helsinki"] == start_days["Zurich"])
))
solver.add(Or(
    And(start_days["Helsinki"] + stay_durations["Helsinki"] == start_days["Hamburg"]),
    And(start_days["Hamburg"] + stay_durations["Hamburg"] == start_days["Helsinki"])
))
solver.add(Or(
    And(start_days["Zurich"] + stay_durations["Zurich"] == start_days["Bucharest"]),
    And(start_days["Bucharest"] + stay_durations["Bucharest"] == start_days["Zurich"])
))
solver.add(Or(
    And(start_days["Zurich"] + stay_durations["Zurich"] == start_days["Split"]),
    And(start_days["Split"] + stay_durations["Split"] == start_days["Zurich"])
))
solver.add(Or(
    And(start_days["Helsinki"] + stay_durations["Helsinki"] == start_days["Split"]),
    And(start_days["Split"] + stay_durations["Split"] == start_days["Helsinki"])
))
solver.add(Or(
    And(start_days["Split"] + stay_durations["Split"] == start_days["Hamburg"]),
    And(start_days["Hamburg"] + stay_durations["Hamburg"] == start_days["Split"])
))

# Ensure all start days are within the valid range
for city in cities:
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] <= total_days - stay_durations[city] + 1)

# Ensure no overlapping stays
for i in range(len(cities)):
    for j in range(i + 1, len(cities)):
        city_i = cities[i]
        city_j = cities[j]
        solver.add(Or(
            start_days[city_i] + stay_durations[city_i] <= start_days[city_j],
            start_days[city_j] + stay_durations[city_j] <= start_days[city_i]
        ))

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city in cities:
        start_day = model[start_days[city]].as_long()
        end_day = start_day + stay_durations[city] - 1
        if start_day == end_day:
            itinerary.append({"day_range": f"Day {start_day}", "place": city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    
    # Add flight days
    for i in range(len(itinerary) - 1):
        end_day = int(itinerary[i]["day_range"].split(" ")[1].split("-")[-1])
        start_day_next = int(itinerary[i+1]["day_range"].split(" ")[1].split("-")[0])
        if end_day < start_day_next:
            flight_day = end_day
            departure_city = itinerary[i]["place"]
            arrival_city = itinerary[i+1]["place"]
            itinerary.append({"day_range": f"Day {flight_day}", "place": departure_city})
            itinerary.append({"day_range": f"Day {flight_day}", "place": arrival_city})
    
    # Sort the itinerary by day range
    itinerary.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
    
    print({"itinerary": itinerary})
else:
    print("No solution found")