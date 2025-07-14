from z3 import *

# Define the number of days and cities
num_days = 22
cities = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Istanbul", "Milan", "Vilnius", "Frankfurt"]

# Create a solver instance
solver = Solver()

# Create a boolean variable for each day and each city
presence = [[Bool(f"d{d}_c{c}") for c in range(len(cities))] for d in range(num_days)]

# Add constraints for staying in each city for the required number of days
required_stays = {
    "Brussels": 3,
    "Helsinki": 3,
    "Split": 4,
    "Dubrovnik": 2,
    "Istanbul": 5,
    "Milan": 4,
    "Vilnius": 5,
    "Frankfurt": 3
}

for city, days in required_stays.items():
    c_index = cities.index(city)
    # Ensure the person stays in the city for the exact number of days
    solver.add(Sum([If(presence[d][c_index], 1, 0) for d in range(num_days)]) == days)

# Add constraints for specific events
# Annual show in Istanbul from day 1 to day 5
for d in range(5):
    solver.add(presence[d][cities.index("Istanbul")])

# Workshop in Vilnius between day 18 and day 22
for d in range(17, 22):
    solver.add(presence[d][cities.index("Vilnius")])

# Wedding in Frankfurt between day 16 and day 18
for d in range(15, 18):
    solver.add(presence[d][cities.index("Frankfurt")])

# Add constraints for direct flights
direct_flights = [
    ("Milan", "Frankfurt"), ("Split", "Frankfurt"), ("Milan", "Split"),
    ("Brussels", "Vilnius"), ("Brussels", "Helsinki"), ("Istanbul", "Brussels"),
    ("Milan", "Vilnius"), ("Brussels", "Milan"), ("Istanbul", "Helsinki"),
    ("Helsinki", "Vilnius"), ("Helsinki", "Dubrovnik"), ("Split", "Vilnius"),
    ("Dubrovnik", "Istanbul"), ("Istanbul", "Milan"), ("Helsinki", "Frankfurt"),
    ("Istanbul", "Vilnius"), ("Split", "Helsinki"), ("Milan", "Helsinki"),
    ("Istanbul", "Frankfurt"), ("Brussels", "Frankfurt"), ("Dubrovnik", "Frankfurt"),
    ("Frankfurt", "Vilnius")
]

# Ensure that if the person is in city A on day X and flies to city B on day X+1,
# they must be in city B on day X+1 and not in city A on day X+1
for d in range(num_days - 1):
    for (city_a, city_b) in direct_flights:
        a_index = cities.index(city_a)
        b_index = cities.index(city_b)
        # If in city A on day d, can only be in city A or city B on day d+1
        solver.add(Or(Not(presence[d][a_index]), presence[d + 1][b_index]))
        # If in city B on day d, can only be in city A or city B on day d+1
        solver.add(Or(Not(presence[d][b_index]), presence[d + 1][a_index]))

# Ensure that the person is in exactly one city per day
for d in range(num_days):
    solver.add(Or([presence[d][c] for c in range(len(cities))]))
    for c1 in range(len(cities)):
        for c2 in range(c1 + 1, len(cities)):
            solver.add(Or(Not(presence[d][c1]), Not(presence[d][c2])))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    current_city = None
    current_start_day = None

    for d in range(num_days):
        for c in range(len(cities)):
            if model.evaluate(presence[d][c]):
                if current_city != cities[c]:
                    if current_city is not None:
                        itinerary.append({"day_range": f"Day {current_start_day + 1}-{d + 1}", "place": current_city})
                    current_city = cities[c]
                    current_start_day = d
                break

    # Add the last day range
    if current_city is not None:
        itinerary.append({"day_range": f"Day {current_start_day + 1}-{num_days}", "place": current_city})

    # Adjust for flight days
    adjusted_itinerary = []
    i = 0
    while i < len(itinerary):
        entry = itinerary[i]
        start, end = map(int, entry["day_range"].split('-')[1].split(' '))
        if i + 1 < len(itinerary) and int(itinerary[i + 1]["day_range"].split('-')[1].split(' ')[0]) == end:
            adjusted_itinerary.append(entry)
            adjusted_itinerary.append({"day_range": f"Day {end}", "place": itinerary[i + 1]["place"]})
            i += 2
        else:
            adjusted_itinerary.append(entry)
            i += 1

    print({"itinerary": adjusted_itinerary})
else:
    print("No solution found")