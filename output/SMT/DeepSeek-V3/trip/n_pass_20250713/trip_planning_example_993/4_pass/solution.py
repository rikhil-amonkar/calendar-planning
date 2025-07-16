from z3 import *

def solve_itinerary():
    # Define cities and their indices
    cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Days from 1 to 15
    days = list(range(1, 16))
    
    # Create solver
    s = Solver()
    
    # Decision variables: city for each day
    city_vars = [Int(f"day_{day}") for day in days]
    for var in city_vars:
        s.add(var >= 0, var < len(cities))
    
    # Flight connections (bidirectional)
    connections = [
        ("London", "Amsterdam"),
        ("Vilnius", "Frankfurt"),
        ("Riga", "Vilnius"),
        ("Riga", "Stockholm"),
        ("London", "Bucharest"),
        ("Amsterdam", "Stockholm"),
        ("Amsterdam", "Frankfurt"),
        ("Frankfurt", "Stockholm"),
        ("Bucharest", "Riga"),
        ("Amsterdam", "Riga"),
        ("Amsterdam", "Bucharest"),
        ("Riga", "Frankfurt"),
        ("Bucharest", "Frankfurt"),
        ("London", "Frankfurt"),
        ("London", "Stockholm"),
        ("Amsterdam", "Vilnius")
    ]
    
    # Convert connections to city indices
    flight_conn = [(city_idx[fr], city_idx[to]) for fr, to in connections]
    flight_conn += [(to, fr) for fr, to in flight_conn]  # Make bidirectional
    
    # Flight transition constraints
    for i in range(len(days)-1):
        current = city_vars[i]
        next_city = city_vars[i+1]
        # Either stay or take a direct flight
        s.add(Or(
            current == next_city,
            *[And(current == fr, next_city == to) for fr, to in flight_conn]
        ))
    
    # Duration constraints
    s.add(Sum([If(var == city_idx["Riga"], 1, 0) for var in city_vars]) == 2)
    s.add(Sum([If(var == city_idx["Frankfurt"], 1, 0) for var in city_vars]) == 3)
    s.add(Sum([If(var == city_idx["Amsterdam"], 1, 0) for var in city_vars]) == 2)
    s.add(Sum([If(var == city_idx["Vilnius"], 1, 0) for var in city_vars]) == 5)
    s.add(Sum([If(var == city_idx["London"], 1, 0) for var in city_vars]) == 2)
    s.add(Sum([If(var == city_idx["Stockholm"], 1, 0) for var in city_vars]) == 3)
    s.add(Sum([If(var == city_idx["Bucharest"], 1, 0) for var in city_vars]) == 4)
    
    # Event constraints
    # Amsterdam meeting between day 2-3
    s.add(Or(
        city_vars[1] == city_idx["Amsterdam"],  # Day 2
        city_vars[2] == city_idx["Amsterdam"]   # Day 3
    ))
    
    # Vilnius workshop between day 7-11
    s.add(Or([city_vars[i] == city_idx["Vilnius"] for i in range(6, 11)]))
    
    # Stockholm wedding between day 13-15
    s.add(Or([city_vars[i] == city_idx["Stockholm"] for i in range(12, 15)]))
    
    # Solve and format itinerary
    if s.check() == sat:
        model = s.model()
        day_assignments = [model.evaluate(var).as_long() for var in city_vars]
        
        itinerary = []
        current_city = day_assignments[0]
        start_day = 1
        
        for i in range(1, len(days)):
            if day_assignments[i] != current_city:
                # Add stay before flight
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": cities[current_city]})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": cities[current_city]})
                # Add flight day
                itinerary.append({"day_range": f"Day {i}", "place": cities[current_city]})
                itinerary.append({"day_range": f"Day {i}", "place": cities[day_assignments[i]]})
                current_city = day_assignments[i]
                start_day = i + 1
        
        # Add last stay
        if start_day == len(days):
            itinerary.append({"day_range": f"Day {start_day}", "place": cities[current_city]})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{len(days)}", "place": cities[current_city]})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))