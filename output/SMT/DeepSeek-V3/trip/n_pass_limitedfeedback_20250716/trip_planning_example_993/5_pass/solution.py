from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
    city_days = {
        "Riga": 2,
        "Frankfurt": 3,
        "Amsterdam": 2,
        "Vilnius": 5,
        "London": 2,
        "Stockholm": 3,
        "Bucharest": 4
    }
    
    # Direct flights (bidirectional)
    direct_flights = [
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
    
    # Create all possible flight connections (bidirectional)
    all_flights = set()
    for a, b in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(1, 16)]
    
    # City to integer mapping
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Solver
    s = Solver()
    
    # Each day must be assigned to a city
    for day in days:
        s.add(Or([day == city_to_int[city] for city in cities]))
    
    # Total days in each city must match requirements
    for city in cities:
        total = Sum([If(day == city_to_int[city], 1, 0) for day in days])
        s.add(total == city_days[city])
    
    # Special constraints
    # 1. Amsterdam visit between day 2 and 3
    s.add(Or(days[1] == city_to_int["Amsterdam"], days[2] == city_to_int["Amsterdam"]))
    
    # 2. Vilnius workshop between day 7-11 (must be there at least one day)
    s.add(Or([days[i] == city_to_int["Vilnius"] for i in range(6, 11)]))
    
    # 3. Stockholm wedding between day 13-15 (must be there at least one day)
    s.add(Or([days[i] == city_to_int["Stockholm"] for i in range(12, 15)]))
    
    # Flight connectivity between consecutive days
    for i in range(14):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            *[And(current == city_to_int[a], next_day == city_to_int[b]) for (a, b) in all_flights]
        ))
    
    # Additional constraints to help the solver
    # Avoid too many single-day stays unless necessary
    for i in range(1, 14):
        s.add(Or(
            days[i] == days[i-1],
            days[i] == days[i+1],
            days[i-1] == days[i+1]
        ))
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(15):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": day_num, "city": city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))