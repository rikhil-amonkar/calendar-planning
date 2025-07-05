from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Venice": 3,  # Note: Typo, should be Venice
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5
    }
    
    # Correct the typo
    cities["Venice"] = cities.pop("Venice", 3)
    
    # Direct flights adjacency list
    direct_flights = {
        "Bucharest": ["Manchester", "Valencia", "Vienna", "Munich", "Santorini"],
        "Munich": ["Venice", "Porto", "Manchester", "Reykjavik", "Vienna", "Bucharest", "Tallinn", "Valencia"],
        "Santorini": ["Manchester", "Venice", "Vienna", "Bucharest"],
        "Vienna": ["Reykjavik", "Valencia", "Manchester", "Porto", "Venice", "Bucharest", "Santorini", "Munich"],
        "Venice": ["Munich", "Santorini", "Manchester", "Vienna"],
        "Manchester": ["Bucharest", "Santorini", "Vienna", "Porto", "Venice", "Munich"],
        "Porto": ["Munich", "Vienna", "Manchester", "Valencia"],
        "Valencia": ["Vienna", "Bucharest", "Porto", "Munich"],
        "Reykjavik": ["Vienna", "Munich"],
        "Tallinn": ["Munich"]
    }
    
    # Fixed constraints
    fixed_constraints = [
        ("Munich", 4, 6),  # Days 4-6 in Munich
        ("Santorini", 8, 10),  # Days 8-10 in Santorini
        ("Valencia", 14, 15)  # Days 14-15 in Valencia
    ]
    
    num_days = 24
    city_list = list(cities.keys())
    
    # Create Z3 variables: day[i] is the city visited on day i (1-based)
    day = [Int(f"day_{i}") for i in range(1, num_days + 1)]
    
    # Each day's assignment must be a valid city (0 to len(city_list)-1)
    city_ints = {city: idx for idx, city in enumerate(city_list)}
    city_vars = [city_ints[city] for city in city_list]
    
    s = Solver()
    
    for d in day:
        s.add(Or([d == city_ints[city] for city in city_list]))
    
    # Add duration constraints for each city
    for city in city_list:
        total_days = sum([If(day[i] == city_ints[city], 1, 0) for i in range(num_days)])
        s.add(total_days == cities[city])
    
    # Add fixed constraints
    for city, start, end in fixed_constraints:
        for d in range(start - 1, end):
            s.add(day[d] == city_ints[city])
    
    # Flight constraints: transitions must be via direct flights
    for i in range(num_days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # Allow staying in the same city or moving to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_ints[city1], next_city == city_ints[city2])
              for city1 in city_list for city2 in direct_flights.get(city1, [])]
        ))
    
    # Check if the problem is solvable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        # Generate the itinerary day by day
        day_assignments = []
        for i in range(num_days):
            city_idx = model.evaluate(day[i]).as_long()
            city = city_list[city_idx]
            day_assignments.append(city)
        
        # Process day_assignments to create the itinerary with flight days
        i = 0
        while i < num_days:
            current_city = day_assignments[i]
            start = i + 1  # converting to 1-based
            # Find the consecutive days in the same city
            j = i
            while j < num_days and day_assignments[j] == current_city:
                j += 1
            end = j  # converting to 1-based, end is exclusive
            
            if start == end:
                pass  # shouldn't happen
            else:
                day_range = f"Day {start}-{end}" if (end - start) >= 1 else f"Day {start}"
                itinerary.append({"day_range": day_range, "place": current_city})
            
            if j < num_days:
                next_city = day_assignments[j]
                # Flight day: add entries for both departure and arrival
                itinerary.append({"day_range": f"Day {j}", "place": current_city})
                itinerary.append({"day_range": f"Day {j}", "place": next_city})
            
            i = j
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))