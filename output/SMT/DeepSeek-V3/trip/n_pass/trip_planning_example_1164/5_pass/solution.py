from z3 import *
import json

def solve_itinerary():
    # Cities and their required stay durations
    cities = {
        "Reykjavik": 2,
        "Stockholm": 2,
        "Porto": 5,
        "Nice": 3,
        "Venice": 4,
        "Vienna": 3,
        "Split": 3,
        "Copenhagen": 2
    }
    
    # Direct flight connections (bidirectional)
    direct_flights = {
        "Copenhagen": ["Vienna", "Split", "Nice", "Porto", "Venice", "Reykjavik", "Stockholm"],
        "Nice": ["Stockholm", "Reykjavik", "Porto", "Venice", "Vienna", "Copenhagen"],
        "Split": ["Copenhagen", "Stockholm", "Vienna"],
        "Reykjavik": ["Nice", "Vienna", "Copenhagen", "Stockholm"],
        "Stockholm": ["Nice", "Copenhagen", "Split", "Vienna", "Reykjavik"],
        "Venice": ["Nice", "Vienna", "Copenhagen"],
        "Vienna": ["Copenhagen", "Nice", "Reykjavik", "Stockholm", "Venice", "Split", "Porto"],
        "Porto": ["Nice", "Copenhagen", "Vienna"]
    }
    
    # Create Z3 variables
    city_start = {city: Int(f'start_{city}') for city in cities}
    city_end = {city: Int(f'end_{city}') for city in cities}
    
    s = Solver()
    
    # Basic constraints
    for city in cities:
        s.add(city_start[city] >= 1)
        s.add(city_end[city] <= 17)
        s.add(city_end[city] == city_start[city] + cities[city] - 1)
    
    # No overlapping stays except for flight days
    for city1 in cities:
        for city2 in cities:
            if city1 != city2:
                s.add(Or(
                    city_end[city1] < city_start[city2],
                    city_end[city2] < city_start[city1]
                ))
    
    # Flight connections between consecutive cities
    city_list = list(cities.keys())
    for i in range(len(city_list)-1):
        city1 = city_list[i]
        city2 = city_list[i+1]
        s.add(Or(
            city2 in direct_flights[city1],
            city1 in direct_flights[city2]
        ))
        s.add(city_start[city2] == city_end[city1] + 1)
    
    # Specific constraints
    # Reykjavik must include day 3 or 4
    s.add(Or(
        And(city_start["Reykjavik"] <= 3, city_end["Reykjavik"] >= 3),
        And(city_start["Reykjavik"] <= 4, city_end["Reykjavik"] >= 4)
    ))
    
    # Stockholm must include day 4 or 5
    s.add(Or(
        And(city_start["Stockholm"] <= 4, city_end["Stockholm"] >= 4),
        And(city_start["Stockholm"] <= 5, city_end["Stockholm"] >= 5)
    ))
    
    # Porto wedding between days 13-17
    s.add(city_start["Porto"] <= 13)
    s.add(city_end["Porto"] >= 13)
    
    # Vienna workshop between days 11-13
    s.add(city_start["Vienna"] <= 11)
    s.add(city_end["Vienna"] >= 13)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        
        # Get start/end days
        stays = []
        for city in cities:
            start = m.evaluate(city_start[city]).as_long()
            end = m.evaluate(city_end[city]).as_long()
            stays.append((start, end, city))
        
        # Sort by start day
        stays.sort()
        
        # Build itinerary
        itinerary = []
        for i, (start, end, city) in enumerate(stays):
            # Add stay
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            
            # Add flight if not last city
            if i < len(stays)-1:
                next_city = stays[i+1][2]
                itinerary.append({"day_range": f"Day {end}", "place": city})
                itinerary.append({"day_range": f"Day {end}", "place": next_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))