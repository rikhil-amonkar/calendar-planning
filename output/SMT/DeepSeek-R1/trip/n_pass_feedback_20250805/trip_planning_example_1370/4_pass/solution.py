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

# Precompute allowed city pairs (as indices)
allowed_pairs = []
for i, city_i in enumerate(city_list):
    neighbors = travel_constraints[city_i]
    for neighbor in neighbors:
        if neighbor in city_list:
            j = city_list.index(neighbor)
            allowed_pairs.append((i, j))

# Amsterdam and Santorini indices
amsterdam_idx = city_list.index("Amsterdam")
santorini_idx = city_list.index("Santorini")

# Try different numbers of cities from 5 to 9
solution_found = False
for num_cities in range(9, 4, -1):  # Try 9 down to 5 cities
    s = Solver()
    s.set("timeout", 300000)  # 5 minutes timeout

    # City variables for each position
    city_vars = [Int(f'city_{i}') for i in range(num_cities)]
    starts = [Int(f'start_{i}') for i in range(num_cities)]
    ends = [Int(f'end_{i}') for i in range(num_cities)]
    durations = [Int(f'duration_{i}') for i in range(num_cities)]

    # City indices within valid range
    for i in range(num_cities):
        s.add(city_vars[i] >= 0, city_vars[i] < n_cities)
    
    # Distinct cities
    s.add(Distinct(city_vars))
    
    # Start and end cities
    s.add(city_vars[0] == amsterdam_idx)
    s.add(city_vars[num_cities-1] == santorini_idx)
    
    # Travel constraints between consecutive cities
    for i in range(num_cities - 1):
        s.add(Or([And(city_vars[i] == pair[0], city_vars[i+1] == pair[1]) for pair in allowed_pairs]))
    
    # Start and end days
    s.add(starts[0] == 1)
    s.add(ends[num_cities-1] == 30)
    
    # Duration constraints
    for i in range(num_cities):
        s.add(ends[i] == starts[i] + durations[i] - 1)
        s.add(durations[i] >= 1)
    
    # Consecutive city constraints
    for i in range(1, num_cities):
        s.add(starts[i] == ends[i-1] + 2)
    
    # Total stay days: 30 - (num_cities - 1) travel days
    total_stay_days = 30 - (num_cities - 1)
    s.add(sum(durations) == total_stay_days)
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(num_cities):
            city_idx = model.eval(city_vars[i]).as_long()
            city_name = city_list[city_idx]
            start_val = model.eval(starts[i]).as_long()
            end_val = model.eval(ends[i]).as_long()
            itinerary.append({
                'day_range': f"Day {start_val}-{end_val}",
                'place': city_name
            })
        print(f"Plan found with {num_cities} cities: {{'itinerary': {itinerary}}}")
        solution_found = True
        break

if not solution_found:
    print("No valid plan found with 5 to 9 cities.")