from itertools import permutations

# Example data for demonstration
cities = ['CityA', 'CityB', 'CityC', 'CityD', 'CityE']
flights = {
    ('CityA', 'CityB'): 2,  # Flight from CityA to CityB takes 2 days
    ('CityB', 'CityC'): 3,  # Flight from CityB to CityC takes 3 days
    ('CityC', 'CityD'): 4,  # Flight from CityC to CityD takes 4 days
    ('CityD', 'CityE'): 2,  # Flight from CityD to CityE takes 2 days
    ('CityE', 'CityA'): 5   # Flight from CityE to CityA takes 5 days
}

def calculate_total_days(itinerary, flights):
    total_days = 0
    for i in range(len(itinerary) - 1):
        total_days += flights[(itinerary[i], itinerary[i + 1])]
    total_days += flights[(itinerary[-1], itinerary[0])]  # Return to the starting city
    return total_days

# Generate all possible permutations of the cities excluding the starting city
city_permutations = permutations(cities[1:])

# Find the permutation that gives a total of 16 days when including the return trip
best_itinerary = None
for perm in city_permutations:
    itinerary = ['CityA'] + list(perm)
    total_days = calculate_total_days(itinerary, flights)
    if total_days == 16:
        best_itinerary = itinerary
        break

if best_itinerary:
    print("Itinerary:", " -> ".join(best_itinerary))
    print("Total Days:", calculate_total_days(best_itinerary, flights))
else:
    print("No valid itinerary found within 16 days.")