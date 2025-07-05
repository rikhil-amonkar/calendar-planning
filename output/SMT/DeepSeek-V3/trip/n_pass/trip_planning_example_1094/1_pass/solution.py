from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ["Vienna", "Barcelona", "Edinburgh", "Krakow", "Riga", "Hamburg", "Paris", "Stockholm"]
    
    # Direct flights as adjacency list
    direct_flights = {
        "Hamburg": ["Stockholm", "Vienna", "Paris", "Barcelona", "Edinburgh"],
        "Vienna": ["Stockholm", "Hamburg", "Barcelona", "Krakow", "Riga", "Paris"],
        "Paris": ["Edinburgh", "Riga", "Krakow", "Stockholm", "Hamburg", "Barcelona", "Vienna"],
        "Riga": ["Barcelona", "Paris", "Edinburgh", "Stockholm", "Hamburg", "Vienna"],
        "Krakow": ["Barcelona", "Stockholm", "Edinburgh", "Paris", "Vienna"],
        "Barcelona": ["Riga", "Krakow", "Stockholm", "Edinburgh", "Paris", "Hamburg", "Vienna"],
        "Edinburgh": ["Paris", "Stockholm", "Riga", "Barcelona", "Krakow", "Hamburg"],
        "Stockholm": ["Hamburg", "Vienna", "Paris", "Riga", "Krakow", "Barcelona", "Edinburgh"]
    }
    
    # Create solver
    s = Solver()
    
    # Variables: day_1 to day_16, each can be one of the cities
    days = [Int(f"day_{i}") for i in range(1, 17)]
    for day in days:
        s.add(Or([day == cities.index(c) for c in cities]))
    
    # Fixed constraints
    # Paris on day 1 and 2 (wedding)
    s.add(days[0] == cities.index("Paris"))
    s.add(days[1] == cities.index("Paris"))
    
    # Hamburg on day 10 and 11 (conference)
    s.add(days[9] == cities.index("Hamburg"))
    s.add(days[10] == cities.index("Hamburg"))
    
    # Stockholm on day 15 and 16 (relatives)
    s.add(days[14] == cities.index("Stockholm"))
    s.add(days[15] == cities.index("Stockholm"))
    
    # Edinburgh between day 12 and 15 (meet friend)
    s.add(Or([days[i] == cities.index("Edinburgh") for i in range(11, 14)]))  # days 12,13,14 (0-based: 11,12,13)
    
    # Duration constraints
    # Vienna: 4 days
    s.add(Sum([If(days[i] == cities.index("Vienna"), 1, 0) for i in range(16)]) == 4)
    # Barcelona: 2 days
    s.add(Sum([If(days[i] == cities.index("Barcelona"), 1, 0) for i in range(16)]) == 2)
    # Edinburgh: 4 days
    s.add(Sum([If(days[i] == cities.index("Edinburgh"), 1, 0) for i in range(16)]) == 4)
    # Krakow: 3 days
    s.add(Sum([If(days[i] == cities.index("Krakow"), 1, 0) for i in range(16)]) == 3)
    # Riga: 4 days
    s.add(Sum([If(days[i] == cities.index("Riga"), 1, 0) for i in range(16)]) == 4)
    # Hamburg: 2 days (already fixed on 10 and 11)
    s.add(Sum([If(days[i] == cities.index("Hamburg"), 1, 0) for i in range(16)]) == 2)
    # Paris: 2 days (already fixed on 1 and 2)
    s.add(Sum([If(days[i] == cities.index("Paris"), 1, 0) for i in range(16)]) == 2)
    # Stockholm: 2 days (fixed on 15 and 16)
    s.add(Sum([If(days[i] == cities.index("Stockholm"), 1, 0) for i in range(16)]) == 2)
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(15):
        current_city = days[i]
        next_city = days[i+1]
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == cities.index(a), next_city == cities.index(b)) 
                for a in cities for b in direct_flights[a] if b in cities])
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        for day in range(1, 17):
            place_index = model.evaluate(days[day-1]).as_long()
            place = cities[place_index]
            if place != current_place:
                if current_place is not None:
                    # Add the previous stay
                    if start_day == day - 1:
                        itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_place})
                # Add the flight day entries
                if day > 1:
                    prev_place_index = model.evaluate(days[day-2]).as_long()
                    prev_place = cities[prev_place_index]
                    if prev_place != place:
                        itinerary.append({"day_range": f"Day {day}", "place": prev_place})
                        itinerary.append({"day_range": f"Day {day}", "place": place})
                start_day = day
                current_place = place
        # Add the last stay
        if start_day == 16:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-16", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))