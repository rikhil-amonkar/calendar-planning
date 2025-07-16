from z3 import *

def solve_itinerary():
    cities = ["Oslo", "Helsinki", "Edinburgh", "Riga", "Tallinn", "Budapest", "Vilnius", "Porto", "Geneva"]
    
    # Direct flights: each key is a city, and the value is a list of cities it has direct flights to.
    direct_flights = {
        "Porto": ["Oslo", "Edinburgh", "Geneva"],
        "Edinburgh": ["Budapest", "Geneva", "Porto", "Oslo", "Helsinki", "Riga"],
        "Riga": ["Tallinn", "Oslo", "Helsinki", "Vilnius"],
        "Tallinn": ["Vilnius", "Helsinki", "Oslo"],
        "Vilnius": ["Helsinki", "Oslo"],
        "Helsinki": ["Vilnius", "Budapest", "Oslo", "Geneva"],
        "Budapest": ["Geneva", "Oslo"],
        "Geneva": ["Oslo", "Porto", "Budapest"],
        "Oslo": ["Porto", "Riga", "Geneva", "Edinburgh", "Vilnius", "Tallinn", "Helsinki", "Budapest"]
    }
    
    total_days = 25
    solver = Solver()
    
    day_vars = [Int(f"day_{i}") for i in range(total_days)]
    
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    for day in day_vars:
        solver.add(day >= 0, day < len(cities))
    
    # Transition constraints: consecutive days must be the same city or have a direct flight
    for i in range(total_days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        solver.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_int[src], next_city == city_to_int[dst]) 
              for src in direct_flights for dst in direct_flights[src]
        ))
    
    required_days = {
        "Oslo": 2,
        "Helsinki": 2,
        "Edinburgh": 3,
        "Riga": 2,
        "Tallinn": 5,
        "Budapest": 5,
        "Vilnius": 5,
        "Porto": 5,
        "Geneva": 4
    }
    
    for city in cities:
        solver.add(Sum([If(day == city_to_int[city], 1, 0) for day in day_vars]) == required_days[city]
    
    # Tallinn wedding between day 4 and 8 (1-based days 4-8)
    solver.add(Or([day_vars[i] == city_to_int["Tallinn"] for i in range(3, 8)]))
    
    # Meet friend in Oslo on day 24 or 25 (1-based)
    solver.add(Or(day_vars[23] == city_to_int["Oslo"], day_vars[24] == city_to_int["Oslo"]))
    
    if solver.check() == sat:
        model = solver.model()
        sequence = [int_to_city[model.evaluate(day_vars[i]).as_long()] for i in range(total_days)]
        
        itinerary = []
        current_city = sequence[0]
        start_day = 1
        
        for i in range(1, total_days):
            if sequence[i] != sequence[i-1]:
                # Flight occurs on day i+1 (1-based)
                # Add stay in current_city from start_day to i
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_city})
                # Add flight day: day i+1 for both cities
                itinerary.append({"day_range": f"Day {i+1}", "place": current_city})
                itinerary.append({"day_range": f"Day {i+1}", "place": sequence[i]})
                current_city = sequence[i]
                start_day = i + 1
        
        # Add the last stay
        if start_day <= total_days:
            if start_day == total_days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found."}

itinerary = solve_itinerary()
print(itinerary)