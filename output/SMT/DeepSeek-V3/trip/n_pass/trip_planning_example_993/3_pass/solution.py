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
    
    # Direct flights as a set of tuples (bidirectional)
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
    # Make flights bidirectional
    all_flights = set()
    for (a, b) in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    # Create Z3 variables: day[i] is the city on day i (1-based)
    days = [Int(f'day_{i}') for i in range(1, 16)]  # days 1 to 15
    
    # Create a mapping from city names to integers
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Solver
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == city_to_int[city] for city in cities]))
    
    # Constraints for the number of days in each city
    for city in cities:
        total_days = Sum([If(day == city_to_int[city], 1, 0) for day in days])
        s.add(total_days == city_days[city])
    
    # Specific constraints:
    # 1. Meet friend in Amsterdam between day 2 and day 3: So Amsterdam must be on day 2 or 3.
    s.add(Or(days[1] == city_to_int["Amsterdam"], days[2] == city_to_int["Amsterdam"]))
    
    # 2. Workshop in Vilnius between day 7 and 11: So Vilnius must be on at least one of days 7-11.
    s.add(Or([days[i] == city_to_int["Vilnius"] for i in range(6, 11)]))  # days 7-11 are indices 6-10 (0-based)
    
    # 3. Wedding in Stockholm between day 13 and 15: So Stockholm must be on at least one of days 13-15.
    s.add(Or([days[i] == city_to_int["Stockholm"] for i in range(12, 15)]))  # days 13-15 are indices 12-14
    
    # Flight connectivity: For consecutive days, either same city or connected by a direct flight.
    for i in range(14):  # days 1..15, compare i and i+1 (0-based)
        current_day = days[i]
        next_day = days[i+1]
        s.add(Or(
            current_day == next_day,  # same city
            *[And(current_day == city_to_int[a], next_day == city_to_int[b]) for (a, b) in all_flights]
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(15):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": day_num, "city": city})
        
        # Format the output as required
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))