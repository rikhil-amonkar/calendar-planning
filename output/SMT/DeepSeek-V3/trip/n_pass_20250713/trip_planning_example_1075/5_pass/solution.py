from z3 import *
import json

def solve_itinerary():
    # Adjusted city days to fit within 25 days total
    cities = {
        "Vienna": 3,
        "Lyon": 2,
        "Edinburgh": 4,
        "Reykjavik": 3,
        "Stuttgart": 3,
        "Manchester": 2,
        "Split": 5,
        "Prague": 3
    }
    # Total: 3+2+4+3+3+2+5+3 = 25 days

    # Direct flights (undirected)
    direct_flights = {
        "Reykjavik": ["Stuttgart", "Vienna", "Prague"],
        "Stuttgart": ["Reykjavik", "Split", "Vienna", "Edinburgh", "Manchester"],
        "Vienna": ["Stuttgart", "Prague", "Manchester", "Lyon", "Split", "Reykjavik"],
        "Prague": ["Manchester", "Edinburgh", "Vienna", "Split", "Lyon", "Reykjavik"],
        "Edinburgh": ["Prague", "Stuttgart"],
        "Manchester": ["Prague", "Vienna", "Split", "Stuttgart"],
        "Split": ["Stuttgart", "Manchester", "Vienna", "Prague", "Lyon"],
        "Lyon": ["Vienna", "Split", "Prague"]
    }

    total_days = 25
    s = Solver()

    # Day variables (1-based)
    day_city = [Int(f"day_{i}") for i in range(1, total_days+1)]

    # City IDs
    city_ids = {city: idx for idx, city in enumerate(cities.keys(), 1)}
    id_to_city = {v: k for k, v in city_ids.items()}

    # Each day must be one of the cities
    for day in day_city:
        s.add(Or([day == cid for cid in city_ids.values()]))

    # Fixed periods
    for day in range(5, 9):  # Edinburgh days 5-8
        s.add(day_city[day-1] == city_ids["Edinburgh"])
    for day in range(19, 24):  # Split days 19-23
        s.add(day_city[day-1] == city_ids["Split"])

    # Total days per city
    for city, days in cities.items():
        s.add(Sum([If(day == city_ids[city], 1, 0) for day in day_city]) == days)

    # Flight connections
    flight_options = []
    for c1 in direct_flights:
        for c2 in direct_flights[c1]:
            flight_options.append(And(day_city[i] == city_ids[c1], day_city[i+1] == city_ids[c2]))
    
    for i in range(total_days-1):
        s.add(Implies(day_city[i] != day_city[i+1], Or(flight_options)))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        for day in range(total_days):
            city_id = model.evaluate(day_city[day]).as_long()
            city = id_to_city[city_id]
            
            if city != current_city:
                if current_city is not None:
                    if start_day == day:
                        itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
                    # Add flight day
                    itinerary.append({"day_range": f"Day {day+1}", "place": current_city})
                    itinerary.append({"day_range": f"Day {day+1}", "place": city})
                current_city = city
                start_day = day + 1
        
        # Add last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        print("No valid itinerary found")
        return {"itinerary": []}

result = solve_itinerary()
print(json.dumps(result, indent=2))