from z3 import *
import json

def solve_itinerary():
    # Cities and their required stay days
    cities = {
        "Frankfurt": 4,
        "Salzburg": 5,
        "Athens": 5,
        "Reykjavik": 5,
        "Bucharest": 3,
        "Valencia": 2,
        "Vienna": 5,
        "Amsterdam": 3,
        "Stockholm": 3,
        "Riga": 3
    }
    
    # Direct flights (undirected, treated as bidirectional)
    direct_flights = [
        ("Valencia", "Frankfurt"),
        ("Vienna", "Bucharest"),
        ("Valencia", "Athens"),
        ("Athens", "Bucharest"),
        ("Riga", "Frankfurt"),
        ("Stockholm", "Athens"),
        ("Amsterdam", "Bucharest"),
        ("Athens", "Riga"),
        ("Amsterdam", "Frankfurt"),
        ("Stockholm", "Vienna"),
        ("Vienna", "Riga"),
        ("Amsterdam", "Reykjavik"),
        ("Reykjavik", "Frankfurt"),
        ("Stockholm", "Amsterdam"),
        ("Amsterdam", "Valencia"),
        ("Vienna", "Frankfurt"),
        ("Valencia", "Bucharest"),
        ("Bucharest", "Frankfurt"),
        ("Stockholm", "Frankfurt"),
        ("Valencia", "Vienna"),
        ("Reykjavik", "Athens"),
        ("Frankfurt", "Salzburg"),
        ("Amsterdam", "Vienna"),
        ("Stockholm", "Reykjavik"),
        ("Amsterdam", "Riga"),
        ("Stockholm", "Riga"),
        ("Vienna", "Reykjavik"),
        ("Amsterdam", "Athens"),
        ("Athens", "Frankfurt"),
        ("Vienna", "Athens"),
        ("Riga", "Bucharest")
    ]
    
    # Create a dictionary of adjacent cities
    adjacency = {}
    for city in cities:
        adjacency[city] = []
    for a, b in direct_flights:
        a_norm = a.capitalize()
        b_norm = b.capitalize()
        if b_norm not in adjacency[a_norm]:
            adjacency[a_norm].append(b_norm)
        if a_norm not in adjacency[b_norm]:
            adjacency[b_norm].append(a_norm)
    
    # Days are 1..29
    days = 29
    
    # Create Z3 variables: assign each day to a city
    assignments = [Int(f"day_{i}") for i in range(1, days + 1)]
    
    # Create a mapping from city names to integers
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day's assignment must be a valid city ID
    for day in assignments:
        s.add(day >= 0, day < len(cities))
    
    # Constraint: consecutive days must be either same city or adjacent
    for i in range(days - 1):
        current_city = assignments[i]
        next_city = assignments[i + 1]
        # Either same city or adjacent
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_ids[a], next_city == city_ids[b]) 
              for a in cities for b in adjacency[a] if a != b]
        ))
    
    # Duration constraints: total days per city must match
    for city, duration in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(assignments[i] == city_id, 1, 0) for i in range(days)]) == duration)
    
    # Event constraints:
    # Workshop in Athens between day 14 and 18 (inclusive)
    s.add(Or(*[assignments[i] == city_ids["Athens"] for i in range(13, 18)]))  # days are 1-based; 14-18 is indices 13-17
    
    # Annual show in Valencia day 5-6 (indices 4-5)
    s.add(Or(assignments[4] == city_ids["Valencia"], assignments[5] == city_ids["Valencia"]))
    
    # Wedding in Vienna between day 6-10 (indices 5-9)
    s.add(Or(*[assignments[i] == city_ids["Vienna"] for i in range(5, 10)]))
    
    # Meet friend in Stockholm between day 1-3 (indices 0-2)
    s.add(Or(*[assignments[i] == city_ids["Stockholm"] for i in range(0, 3)]))
    
    # Conference in Riga day 18-20 (indices 17-19)
    s.add(Or(*[assignments[i] == city_ids["Riga"] for i in range(17, 20)]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, days + 1):
            city_id = model.evaluate(assignments[day - 1]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": day, "place": city})
        
        # Prepare the output
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))