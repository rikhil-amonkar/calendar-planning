from z3 import *

# Define the travel constraints dictionary
travel_constraints = {
    "Amsterdam": ["Berlin", "Brussels", "Paris"],
    "Athens": ["Santorini", "Rome", "Istanbul"],
    "Barcelona": ["Madrid", "Marseille", "Ibiza"],
    "Berlin": ["Amsterdam", "Prague", "Warsaw"],
    "Brussels": ["Amsterdam", "Paris", "London"],
    "Budapest": ["Vienna", "Krakow", "Zagreb"],
    "Copenhagen": ["Stockholm", "Hamburg", "Oslo"],
    "Dublin": ["Belfast", "Liverpool", "Glasgow"],
    "Edinburgh": ["Dublin", "Glasgow", "York"],
    "Geneva": ["Zurich", "Lyon", "Milan"],
    "Helsinki": ["Tallinn", "Stockholm", "St. Petersburg"],
    "Istanbul": ["Athens", "Sofia", "Ankara"],
    "Krakow": ["Warsaw", "Budapest", "Prague"],
    "Lisbon": ["Porto", "Seville", "Madrid"],
    "London": ["Brussels", "Paris", "Dublin"],
    "Madrid": ["Barcelona", "Lisbon", "Seville"],
    "Milan": ["Geneva", "Zurich", "Venice"],
    "Munich": ["Zurich", "Prague", "Venice"],
    "Paris": ["Brussels", "Amsterdam", "London"],
    "Prague": ["Berlin", "Munich", "Vienna"],
    "Rome": ["Athens", "Milan", "Naples"],
    "Santorini": ["Athens", "Heraklion", "Mykonos"],
    "Seville": ["Lisbon", "Madrid", "Granada"],
    "Split": ["Zagreb", "Dubrovnik", "Budapest"],
    "Vienna": ["Prague", "Budapest", "Munich"],
    "Vilnius": ["Warsaw", "Riga", "Tallinn"],
    "Warsaw": ["Berlin", "Krakow", "Vilnius"],
    "Zagreb": ["Budapest", "Split", "Vienna"],
    "Zurich": ["Geneva", "Munich", "Milan"]
}

# Create a sorted list of cities
city_list = sorted(travel_constraints.keys())
n_cities = len(city_list)

# Build the allowed travel matrix
allowed = [[0] * n_cities for _ in range(n_cities)]
for i, city_i in enumerate(city_list):
    neighbors = travel_constraints[city_i]
    for neighbor in neighbors:
        if neighbor in city_list:
            j = city_list.index(neighbor)
            allowed[i][j] = 1

# Number of cities in the itinerary
num_cities = 9

# Initialize Z3 solver
s = Solver()
s.set("timeout", 300000)  # 5 minutes timeout

# City variables for each position in the itinerary
city_vars = [Int(f'city_{i}') for i in range(num_cities)]

# Start, end, and duration variables for each city
starts = [Int(f'start_{i}') for i in range(num_cities)]
ends = [Int(f'end_{i}') for i in range(num_cities)]
durations = [Int(f'duration_{i}') for i in range(num_cities)]

# Constraints

# 1. Each city_var must be within [0, n_cities-1]
for i in range(num_cities):
    s.add(city_vars[i] >= 0)
    s.add(city_vars[i] < n_cities)

# 2. Distinct cities
s.add(Distinct(city_vars))

# 3. First city is Amsterdam
s.add(city_vars[0] == city_list.index("Amsterdam"))

# 4. Last city is Santorini
s.add(city_vars[num_cities-1] == city_list.index("Santorini"))

# 5. Travel constraints between consecutive cities
for i in range(num_cities - 1):
    idx_i = city_vars[i]
    idx_j = city_vars[i+1]
    s.add(allowed[idx_i][idx_j] == 1)

# 6. First city starts at day 1
s.add(starts[0] == 1)

# 7. Last city ends at day 30
s.add(ends[num_cities-1] == 30)

# 8. For each city: end = start + duration - 1
for i in range(num_cities):
    s.add(ends[i] == starts[i] + durations[i] - 1)

# 9. Consecutive cities: next start = previous end + 2 (accounting for travel day)
for i in range(1, num_cities):
    s.add(starts[i] == ends[i-1] + 2)

# 10. Each duration at least 1
for i in range(num_cities):
    s.add(durations[i] >= 1)

# 11. Sum of durations = 22 (since 30 days total - 8 travel days)
s.add(sum(durations) == 22)

# Check and get the model
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(num_cities):
        city_idx = model.eval(city_vars[i]).as_long()
        city_name = city_list[city_idx]
        start_val = model.eval(starts[i]).as_long()
        end_val = model.eval(ends[i]).as_long()
        duration_val = model.eval(durations[i]).as_long()
        itinerary.append({
            'day_range': f"Day {start_val}-{end_val}",
            'place': city_name
        })
    print(f"Plan found: {{'itinerary': {itinerary}}}")
else:
    print("No valid plan found.")