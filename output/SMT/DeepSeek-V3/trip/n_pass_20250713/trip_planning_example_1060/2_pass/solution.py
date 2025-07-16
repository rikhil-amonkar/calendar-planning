from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ["Stuttgart", "Istanbul", "Vilnius", "Seville", "Geneva", "Valencia", "Munich", "Reykjavik"]
    
    # Total days
    total_days = 25
    
    # Required days in each city
    required_days = {
        "Stuttgart": 4,
        "Istanbul": 4,
        "Vilnius": 4,
        "Seville": 3,
        "Geneva": 5,
        "Valencia": 5,
        "Munich": 3,
        "Reykjavik": 4
    }
    
    # Direct flights (bidirectional unless specified)
    direct_flights = {
        "Geneva": ["Istanbul", "Munich", "Valencia"],
        "Istanbul": ["Geneva", "Stuttgart", "Valencia", "Vilnius", "Munich"],
        "Reykjavik": ["Munich", "Stuttgart"],
        "Stuttgart": ["Valencia", "Reykjavik", "Istanbul"],
        "Munich": ["Reykjavik", "Geneva", "Vilnius", "Seville", "Istanbul"],
        "Valencia": ["Stuttgart", "Seville", "Istanbul", "Geneva", "Munich"],
        "Seville": ["Valencia", "Munich"],
        "Vilnius": ["Istanbul", "Munich"]
    }
    
    # Create a solver instance
    solver = Solver()
    
    # Variables: day[i] is the city on day i (1-based)
    day = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    # Assign each day to a city (represented by an integer)
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints: each day must be assigned to a valid city
    for d in day:
        solver.add(d >= 0, d < len(cities))
    
    # Fixed constraints:
    # Reykjavik: workshop between day 1 and 4 (so days 1, 2, 3, 4)
    for i in range(1, 5):
        solver.add(day[i-1] == city_to_int["Reykjavik"])
    
    # Stuttgart: conference on day 4 and 7. Day 4 is Reykjavik, so day 7 must be Stuttgart.
    solver.add(day[6] == city_to_int["Stuttgart"])  # day 7 is index 6
    
    # Munich: annual show from day 13 to 15 (days 13, 14, 15)
    for i in range(13, 16):
        solver.add(day[i-1] == city_to_int["Munich"])
    
    # Istanbul: relatives between day 19 and 22 (19, 20, 21, 22)
    for i in range(19, 23):
        solver.add(day[i-1] == city_to_int["Istanbul"])
    
    # Constraints for total days in each city
    for city in cities:
        count = Sum([If(day[i] == city_to_int[city], 1, 0) for i in range(total_days)])
        solver.add(count == required_days[city])
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(total_days - 1):
        current_city_var = day[i]
        next_city_var = day[i+1]
        # Create a condition that if current_city_var != next_city_var, then there must be a direct flight
        constraint = Or([And(current_city_var == city_to_int[a], next_city_var == city_to_int[b]) 
                         for a in direct_flights for b in direct_flights[a]])
        solver.add(Implies(current_city_var != next_city_var, constraint))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        
        # Determine the day ranges for each city
        current_city = None
        start_day = 1
        
        for i in range(total_days):
            city_idx = model.evaluate(day[i]).as_long()
            city = int_to_city[city_idx]
            
            if current_city is None:
                current_city = city
                start_day = i + 1
            elif city != current_city:
                # Add the previous city's stay
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_city})
                # Add the flight day entries for both cities
                itinerary.append({"day_range": f"Day {i+1}", "place": current_city})
                itinerary.append({"day_range": f"Day {i+1}", "place": city})
                current_city = city
                start_day = i + 1
        
        # Add the last city's stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))