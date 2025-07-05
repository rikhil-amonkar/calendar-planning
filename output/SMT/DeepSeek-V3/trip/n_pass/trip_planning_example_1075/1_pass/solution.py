from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4
    }
    
    # Direct flights adjacency list
    direct_flights = {
        "Reykjavik": ["Stuttgart", "Vienna", "Prague"],
        "Stuttgart": ["Reykjavik", "Split", "Vienna", "Edinburgh", "Manchester"],
        "Vienna": ["Stuttgart", "Prague", "Manchester", "Lyon", "Split", "Reykjavik"],
        "Prague": ["Manchester", "Edinburgh", "Vienna", "Split", "Lyon", "Reykjavik"],
        "Edinburgh": ["Prague", "Stuttgart"],
        "Manchester": ["Prague", "Vienna", "Split", "Stuttgart"],
        "Split": ["Stuttgart", "Manchester", "Prague", "Vienna", "Lyon"],
        "Lyon": ["Vienna", "Split", "Prague"]
    }
    
    # Total days
    total_days = 25
    
    # Fixed events
    # Edinburgh show from day 5 to 8 (inclusive), so Edinburgh must be visited from day 5-8
    # Wedding in Split between day 19 and 23 (inclusive), so Split must include these days
    
    # We need to model the itinerary as a sequence of stays, each with a start and end day, and city.
    # However, modeling this directly is complex. Instead, we can model the assignment of cities to days,
    # ensuring that transitions between cities are via direct flights, and the total days per city match.
    
    # Create a list of days (1..25)
    days = list(range(1, total_days + 1))
    
    # Create a Z3 solver
    s = Solver()
    
    # Variables: for each day, the city visited
    day_to_city = {day: Int(f"day_{day}") for day in days}
    
    # Assign each day_to_city to a numeric representation of cities
    city_to_num = {city: idx for idx, city in enumerate(cities.keys(), 1)}
    num_to_city = {idx: city for city, idx in city_to_num.items()}
    
    # Add constraints that each day's city is one of the 8 cities
    for day in days:
        s.add(Or([day_to_city[day] == city_to_num[city] for city in cities]))
    
    # Constraints for transitions: consecutive days must be same city or have a direct flight
    for day in days[:-1]:
        current_city = day_to_city[day]
        next_city = day_to_city[day + 1]
        s.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_to_num[city1], next_city == city_to_num[city2])
                for city1 in cities for city2 in direct_flights.get(city1, [])
            ]
        ))
    
    # Constraints for total days per city
    for city in cities:
        total = 0
        for day in days:
            total += If(day_to_city[day] == city_to_num[city], 1, 0)
        s.add(total == cities[city])
    
    # Edinburgh must be visited from day 5 to 8
    for day in range(5, 9):
        s.add(day_to_city[day] == city_to_num["Edinburgh"])
    
    # Split must include some days between 19 and 23 (at least one day in this range)
    s.add(Or([day_to_city[day] == city_to_num["Split"] for day in range(19, 24)]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the itinerary
        itinerary_days = []
        for day in days:
            city_num = model.evaluate(day_to_city[day]).as_long()
            itinerary_days.append(num_to_city[city_num])
        
        # Now, generate the itinerary in the required format
        itinerary = []
        current_city = itinerary_days[0]
        start_day = 1
        
        for day in range(2, total_days + 1):
            if itinerary_days[day - 1] != current_city:
                # Add the stay before the flight
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                # Add the flight day (current city and new city)
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": itinerary_days[day - 1]})
                # Update current city and start day
                current_city = itinerary_days[day - 1]
                start_day = day
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))