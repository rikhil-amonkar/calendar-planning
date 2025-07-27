import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Porto": 5,
        "Amsterdam": 4,
        "Helsinki": 4,
        "Naples": 4,
        "Brussels": 3,
        "Warsaw": 3,
        "Split": 3,
        "Reykjavik": 5,
        "Lyon": 3,
        "Valencia": 2
    }
    
    # Direct flights: list of tuples
    direct_flights = [
        ("Amsterdam", "Warsaw"),
        ("Helsinki", "Brussels"),
        ("Helsinki", "Warsaw"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Lyon"),
        ("Amsterdam", "Naples"),
        ("Amsterdam", "Reykjavik"),
        ("Naples", "Valencia"),
        ("Porto", "Brussels"),
        ("Amsterdam", "Split"),
        ("Lyon", "Split"),
        ("Warsaw", "Split"),
        ("Porto", "Amsterdam"),
        ("Helsinki", "Split"),
        ("Brussels", "Lyon"),
        ("Porto", "Lyon"),
        ("Reykjavik", "Warsaw"),
        ("Brussels", "Valencia"),
        ("Valencia", "Lyon"),
        ("Porto", "Warsaw"),
        ("Warsaw", "Valencia"),
        ("Amsterdam", "Helsinki"),
        ("Porto", "Valencia"),
        ("Warsaw", "Brussels"),
        ("Warsaw", "Naples"),
        ("Naples", "Split"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Reykjavik"),
        ("Amsterdam", "Valencia"),
        ("Naples", "Brussels")
    ]
    
    # Correct any typos in city names
    corrected_flights = []
    for (a, b) in direct_flights:
        a = a.replace("Brussels", "Brussels").replace("Reykjavik", "Reykjavik")
        b = b.replace("Brussels", "Brussels").replace("Reykjavik", "Reykjavik")
        corrected_flights.append((a, b))
    
    # Create a set of direct flights for quick lookup
    flight_pairs = set()
    for (a, b) in corrected_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Total days
    total_days = 27
    
    # Create Z3 variables for each day: the city for that day
    day_city = [Int(f"day_{i}_city") for i in range(1, total_days + 1)]
    
    # Create a mapping from city names to integers
    city_names = sorted(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_names)}
    int_to_city = {idx: city for city, idx in city_to_int.items()}
    
    s = Solver()
    
    # Constraint: each day's variable must be a valid city index
    for day in day_city:
        s.add(day >= 0, day < len(city_names))
    
    # Fixed events:
    # Porto: days 1-5
    for day in range(1, 6):
        s.add(day_city[day - 1] == city_to_int["Porto"])
    
    # Amsterdam: days 5-8
    for day in range(5, 9):
        s.add(day_city[day - 1] == city_to_int["Amsterdam"])
    
    # Helsinki: days 8-11
    for day in range(8, 12):
        s.add(day_city[day - 1] == city_to_int["Helsinki"])
    
    # Naples: days 17-20
    for day in range(17, 21):
        s.add(day_city[day - 1] == city_to_int["Naples"])
    
    # Brussels: days 20-22
    for day in range(20, 23):
        s.add(day_city[day - 1] == city_to_int["Brussels"])
    
    # Flight constraints: between consecutive days, either stay in same city or take direct flight
    for i in range(total_days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # Either same city or flight exists
        same_city = current_city == next_city
        flight_exists = Or([And(current_city == city_to_int[a], next_city == city_to_int[b]) for (a, b) in flight_pairs])
        s.add(Or(same_city, flight_exists))
    
    # Duration constraints: each city must be visited for exactly the required number of days
    for city, days in cities.items():
        city_idx = city_to_int[city]
        s.add(Sum([If(day_city[i] == city_idx, 1, 0) for i in range(total_days)]) == days)
    
    # Additional constraints to help the solver
    # Ensure we don't have too many consecutive days in one city (except for fixed events)
    max_consecutive = 5
    for i in range(total_days - max_consecutive):
        s.add(Or([day_city[i] != day_city[i + j] for j in range(1, max_consecutive + 1)]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(total_days):
            city_idx = model.evaluate(day_city[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": i + 1, "place": city})
        
        # Verify all constraints are satisfied
        # 1. Check fixed events
        assert all(itinerary[d-1]['place'] == 'Porto' for d in range(1,6))
        assert all(itinerary[d-1]['place'] == 'Amsterdam' for d in range(5,9))
        assert all(itinerary[d-1]['place'] == 'Helsinki' for d in range(8,12))
        assert all(itinerary[d-1]['place'] == 'Naples' for d in range(17,21))
        assert all(itinerary[d-1]['place'] == 'Brussels' for d in range(20,23))
        
        # 2. Check flight connections
        for i in range(total_days - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current_city != next_city:
                assert (current_city, next_city) in flight_pairs or (next_city, current_city) in flight_pairs
        
        # 3. Check day counts
        city_counts = {city: 0 for city in cities}
        for day in itinerary:
            city_counts[day['place']] += 1
        for city, days in cities.items():
            assert city_counts[city] == days
        
        # Convert to the required JSON format
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found."}

# Generate the solution
solution = solve_itinerary()
print(json.dumps(solution, indent=2))