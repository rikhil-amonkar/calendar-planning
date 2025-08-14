import itertools
import json

# Define the cities and their required days
cities = {
    "Oslo": 2,
    "Helsinki": 2,
    "Vilnius": 2,
    "Krakow": 5,
    "Paris": 2,
    "Madrid": 5,
    "Dubrovnik": 3,
    "Mykonos": 4
}

# Define direct flights as a set of tuples (A, B)
direct_flights = {
    ("Oslo", "Krakow"), ("Oslo", "Paris"), ("Paris", "Madrid"), ("Helsinki", "Vilnius"),
    ("Oslo", "Madrid"), ("Oslo", "Helsinki"), ("Helsinki", "Krakow"), ("Dubrovnik", "Helsinki"),
    ("Dubrovnik", "Madrid"), ("Oslo", "Dubrovnik"), ("Krakow", "Paris"), ("Madrid", "Mykonos"),
    ("Oslo", "Vilnius"), ("Krakow", "Vilnius"), ("Helsinki", "Paris"), ("Vilnius", "Paris"),
    ("Helsinki", "Madrid"),
    # Add reverse directions
    ("Krakow", "Oslo"), ("Paris", "Oslo"), ("Madrid", "Paris"), ("Vilnius", "Helsinki"),
    ("Madrid", "Oslo"), ("Helsinki", "Oslo"), ("Krakow", "Helsinki"), ("Helsinki", "Dubrovnik"),
    ("Madrid", "Dubrovnik"), ("Dubrovnik", "Oslo"), ("Paris", "Krakow"), ("Mykonos", "Madrid"),
    ("Vilnius", "Oslo"), ("Vilnius", "Krakow"), ("Paris", "Helsinki"), ("Paris", "Vilnius"),
    ("Madrid", "Helsinki")
}

# Generate all permutations of the cities
city_list = list(cities.keys())
for perm in itertools.permutations(city_list):
    valid = True
    for i in range(len(perm) - 1):
        if (perm[i], perm[i+1]) not in direct_flights:
            valid = False
            break
    if not valid:
        continue

    # Calculate day ranges for each city
    day_ranges = []
    current_day = 1
    for city in perm:
        days_in_city = cities[city]
        day_range = f"Day {current_day}-{current_day + days_in_city - 1}"
        day_ranges.append({"day_range": day_range, "place": city})
        current_day += days_in_city

    # Check if the total days is 18
    if current_day - 1 != 18:
        continue

    # Check Dubrovnik is visited from day 2-4
    dubrovnik_index = perm.index("Dubrovnik")
    dubrovnik_days = cities["Dubrovnik"]
    dubrovnik_start_day = current_day_before = 1
    for i in range(dubrovnik_index):
        current_day_before += cities[perm[i]]
    dubrovnik_end_day = current_day_before + dubrovnik_days - 1
    if not (dubrovnik_start_day + 1 <= 2 and dubrovnik_end_day >= 4):
        continue

    # Check Mykonos is visited from day 15-18
    mykonos_index = perm.index("Mykonos")
    mykonos_start_day = 1
    for i in range(mykonos_index):
        mykonos_start_day += cities[perm[i]]
    mykonos_end_day = mykonos_start_day + cities["Mykonos"] - 1
    if not (15 <= mykonos_start_day and mykonos_end_day >= 18):
        continue

    # Check Oslo is visited for 2 days with arrival between day 1-2
    oslo_index = perm.index("Oslo")
    oslo_start_day = 1
    for i in range(oslo_index):
        oslo_start_day += cities[perm[i]]
    if not (1 <= oslo_start_day <= 2):
        continue

    # If all constraints are met, output the result
    print(json.dumps({"itinerary": day_ranges}))
    break