from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
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
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("Porto", "Oslo"), ("Porto", "Edinburgh"), ("Porto", "Geneva"),
        ("Edinburgh", "Budapest"), ("Edinburgh", "Geneva"), ("Edinburgh", "Oslo"),
        ("Edinburgh", "Helsinki"), ("Edinburgh", "Riga"),
        ("Riga", "Tallinn"), ("Riga", "Oslo"), ("Riga", "Helsinki"), ("Riga", "Vilnius"),
        ("Tallinn", "Vilnius"), ("Tallinn", "Helsinki"), ("Tallinn", "Oslo"),
        ("Vilnius", "Helsinki"), ("Vilnius", "Oslo"),
        ("Helsinki", "Budapest"), ("Helsinki", "Oslo"), ("Helsinki", "Geneva"),
        ("Budapest", "Geneva"), ("Budapest", "Oslo"),
        ("Geneva", "Oslo"), ("Geneva", "Porto"), ("Geneva", "Budapest")
    ]
    
    total_days = 25
    city_list = list(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_list)}
    
    # Create solver
    solver = Solver()
    solver.set("timeout", 10000)  # 10 second timeout
    
    # Day variables
    day_vars = [Int(f"day_{i}") for i in range(total_days)]
    for day in day_vars:
        solver.add(day >= 0, day < len(city_list))
    
    # Transition constraints
    flight_map = {}
    for src, dst in direct_flights:
        if src not in flight_map:
            flight_map[src] = []
        flight_map[src].append(dst)
    
    for i in range(total_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        options = [current == next_day]  # Stay in same city
        
        for src in flight_map:
            for dst in flight_map[src]:
                options.append(And(current == city_to_int[src], 
                                 next_day == city_to_int[dst]))
        solver.add(Or(options))
    
    # Day count constraints
    for city, days in cities.items():
        solver.add(Sum([If(day_vars[i] == city_to_int[city], 1, 0) 
                   for i in range(total_days)) == days)
    
    # Special constraints
    # Wedding in Tallinn between day 4-8
    solver.add(Or([day_vars[i] == city_to_int["Tallinn"] for i in range(3, 8)]))
    
    # Meet friend in Oslo on day 24 or 25
    solver.add(Or(day_vars[23] == city_to_int["Oslo"], 
                 day_vars[24] == city_to_int["Oslo"]))
    
    # Symmetry breaking - first city is Edinburgh
    solver.add(day_vars[0] == city_to_int["Edinburgh"])
    
    if solver.check() == sat:
        model = solver.model()
        sequence = [city_list[model.evaluate(day_vars[i]).as_long()] 
                   for i in range(total_days)]
        
        # Generate itinerary
        itinerary = []
        current = sequence[0]
        start = 1
        
        for i in range(1, total_days):
            if sequence[i] != sequence[i-1]:
                if start == i:
                    itinerary.append({"day_range": f"Day {start}", "place": current})
                else:
                    itinerary.append({"day_range": f"Day {start}-{i}", "place": current})
                
                itinerary.append({"day_range": f"Day {i+1}", "place": current})
                itinerary.append({"day_range": f"Day {i+1}", "place": sequence[i]})
                current = sequence[i]
                start = i + 1
        
        if start <= total_days:
            if start == total_days:
                itinerary.append({"day_range": f"Day {total_days}", "place": current})
            else:
                itinerary.append({"day_range": f"Day {start}-{total_days}", "place": current})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found within time limit"}

print(solve_itinerary())