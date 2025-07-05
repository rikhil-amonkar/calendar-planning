from z3 import *
import json

def solve_itinerary():
    # Cities and their required stay days
    cities = {
        "Dublin": 5,
        "Helsinki": 3,
        "Riga": 3,
        "Reykjavik": 2,
        "Vienna": 2,
        "Tallinn": 5
    }
    city_list = list(cities.keys())
    n_days = 15
    days = range(1, n_days + 1)
    
    # Direct flights: adjacency list
    direct_flights = {
        "Helsinki": ["Riga", "Dublin", "Tallinn", "Reykjavik"],
        "Riga": ["Helsinki", "Tallinn", "Vienna", "Dublin"],
        "Vienna": ["Riga", "Reykjavik", "Dublin"],
        "Reykjavik": ["Vienna", "Helsinki", "Dublin"],
        "Tallinn": ["Dublin", "Helsinki", "Riga"],
        "Dublin": ["Riga", "Vienna", "Reykjavik", "Helsinki", "Tallinn"]
    }
    
    # Create Z3 variables
    # For each day, which city we're in (None if in transit)
    day_city = [Int(f"day_{d}_city") for d in days]
    s = Solver()
    
    # Each day must be assigned a valid city index (0-5)
    for d in days:
        s.add(day_city[d-1] >= 0, day_city[d-1] < len(city_list))
    
    # Flight transitions must be direct
    for d in range(1, n_days):
        current_city = day_city[d-1]
        next_city = day_city[d]
        s.add(Or(
            current_city == next_city,  # Stay in same city
            And(
                current_city != next_city,
                Or([city_list[next_city] in direct_flights[city_list[current_city]]])
            )
        ))
    
    # Stay duration constraints
    for city_idx, city in enumerate(city_list):
        total_days = sum([If(day_city[d-1] == city_idx, 1, 0) for d in days])
        s.add(total_days == cities[city])
    
    # Specific constraints:
    # 1. Helsinki friends between day 3-5
    helsinki_idx = city_list.index("Helsinki")
    s.add(Or([day_city[d-1] == helsinki_idx for d in range(3, 6)]))
    
    # 2. Vienna show between day 2-3
    vienna_idx = city_list.index("Vienna")
    s.add(Or(day_city[1] == vienna_idx, day_city[2] == vienna_idx))
    
    # 3. Tallinn wedding between day 7-11
    tallinn_idx = city_list.index("Tallinn")
    s.add(Or([day_city[d-1] == tallinn_idx for d in range(7, 12)]))
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Generate day sequence
        day_sequence = [model.evaluate(day_city[d-1]).as_long() for d in days]
        
        # Build itinerary with proper ranges
        current_city = day_sequence[0]
        start_day = 1
        
        for d in range(1, n_days):
            if day_sequence[d] != current_city:
                # Flight day - add both departure and arrival
                itinerary.append({
                    "day_range": f"Day {start_day}-{d}",
                    "place": city_list[current_city]
                })
                itinerary.append({
                    "day_range": f"Day {d}",
                    "place": city_list[current_city]
                })
                itinerary.append({
                    "day_range": f"Day {d}",
                    "place": city_list[day_sequence[d]]
                })
                current_city = day_sequence[d]
                start_day = d + 1
        
        # Add final stay
        itinerary.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": city_list[current_city]
        })
        
        # Remove duplicates and clean up
        unique_itinerary = []
        seen = set()
        for entry in itinerary:
            key = (entry['day_range'], entry['place'])
            if key not in seen:
                seen.add(key)
                unique_itinerary.append(entry)
        
        return {"itinerary": unique_itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))