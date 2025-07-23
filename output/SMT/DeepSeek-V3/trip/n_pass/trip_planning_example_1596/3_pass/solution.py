import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = [
        "Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw",
        "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"
    ]
    
    # Direct flights as a dictionary for quick lookup
    direct_flights = {
        "Budapest": ["Munich", "Vienna", "Warsaw", "Bucharest", "Edinburgh", "Barcelona"],
        "Bucharest": ["Riga", "Munich", "Warsaw", "Vienna", "Budapest", "Barcelona"],
        "Munich": ["Budapest", "Krakow", "Warsaw", "Bucharest", "Barcelona", "Stockholm", "Edinburgh", "Vienna"],
        "Krakow": ["Munich", "Warsaw", "Edinburgh", "Stockholm", "Vienna", "Barcelona"],
        "Barcelona": ["Warsaw", "Munich", "Stockholm", "Riga", "Edinburgh", "Budapest", "Bucharest", "Krakow", "Vienna"],
        "Warsaw": ["Munich", "Krakow", "Barcelona", "Bucharest", "Vienna", "Budapest", "Riga", "Stockholm"],
        "Stockholm": ["Edinburgh", "Krakow", "Munich", "Barcelona", "Riga", "Warsaw", "Vienna"],
        "Riga": ["Bucharest", "Barcelona", "Vienna", "Munich", "Warsaw", "Stockholm", "Edinburgh"],
        "Edinburgh": ["Stockholm", "Krakow", "Barcelona", "Budapest", "Munich", "Riga"],
        "Vienna": ["Budapest", "Riga", "Krakow", "Warsaw", "Stockholm", "Munich", "Bucharest", "Barcelona"]
    }
    
    # Required days per city
    required_days = {
        "Bucharest": 2,
        "Krakow": 4,
        "Munich": 3,
        "Barcelona": 5,
        "Warsaw": 5,
        "Budapest": 5,
        "Stockholm": 2,
        "Riga": 5,
        "Edinburgh": 5,
        "Vienna": 5
    }
    
    # Fixed events
    fixed_events = [
        (18, 20, "Munich"),  # Workshop in Munich between day 18-20
        (25, 29, "Warsaw"),  # Conference in Warsaw between day 25-29
        (9, 13, "Budapest"), # Annual show in Budapest between day 9-13
        (17, 18, "Stockholm"), # Meet friends in Stockholm between day 17-18
        (1, 5, "Edinburgh")   # Meet friend in Edinburgh between day 1-5
    ]
    
    # Create Z3 solver
    s = Solver()
    
    # Variables: each day is assigned a city
    day_to_city = [Int(f"day_{i}") for i in range(1, 33)]
    for day in day_to_city:
        s.add(day >= 0, day < len(cities))
    
    # Helper function to get city name from index
    def city_name(index):
        return cities[index]
    
    # Fixed events constraints
    for start, end, city in fixed_events:
        city_idx = cities.index(city)
        for day in range(start, end + 1):
            s.add(day_to_city[day - 1] == city_idx)
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(31):
        current_day = day_to_city[i]
        next_day = day_to_city[i + 1]
        # Either stay in the same city or move to a directly connected city
        same_city = (current_day == next_day)
        possible_flights = []
        for c_idx in range(len(cities)):
            current_city = cities[c_idx]
            for neighbor in direct_flights.get(current_city, []):
                neighbor_idx = cities.index(neighbor)
                possible_flights.append(And(current_day == c_idx, next_day == neighbor_idx))
        s.add(Or(same_city, *possible_flights))
    
    # Duration constraints: each city must be visited exactly required_days times
    for city_idx, city in enumerate(cities):
        count = 0
        for day in day_to_city:
            count += If(day == city_idx, 1, 0)
        s.add(count == required_days[city])
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 33):
            city_idx = model.evaluate(day_to_city[day - 1]).as_long()
            itinerary.append({"day": day, "place": cities[city_idx]})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should have ensured it)
        
        # Prepare the output
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Generate the solution
solution = solve_itinerary()
print(json.dumps(solution, indent=2))