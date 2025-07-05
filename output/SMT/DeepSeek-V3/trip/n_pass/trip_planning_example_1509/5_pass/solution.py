from z3 import *
import json

def solve_itinerary():
    # Cities with their required days
    cities = {
        "Paris": 5,
        "Warsaw": 2,
        "Krakow": 2,
        "Tallinn": 2,
        "Riga": 2,
        "Copenhagen": 5,
        "Helsinki": 5,
        "Oslo": 5,
        "Santorini": 2,
        "Lyon": 4
    }
    
    # Direct flights (bidirectional)
    flights = {
        "Warsaw": ["Riga", "Tallinn", "Copenhagen", "Helsinki", "Paris", "Oslo", "Krakow"],
        "Riga": ["Warsaw", "Paris", "Helsinki", "Oslo", "Tallinn", "Copenhagen"],
        "Tallinn": ["Warsaw", "Oslo", "Helsinki", "Copenhagen", "Paris", "Riga"],
        "Copenhagen": ["Helsinki", "Warsaw", "Santorini", "Krakow", "Riga", "Oslo", "Tallinn", "Paris"],
        "Helsinki": ["Copenhagen", "Warsaw", "Oslo", "Tallinn", "Riga", "Paris", "Krakow"],
        "Oslo": ["Lyon", "Paris", "Riga", "Warsaw", "Helsinki", "Tallinn", "Krakow", "Copenhagen", "Santorini"],
        "Santorini": ["Copenhagen", "Oslo"],
        "Lyon": ["Paris", "Oslo"],
        "Paris": ["Lyon", "Oslo", "Riga", "Tallinn", "Warsaw", "Helsinki", "Krakow", "Copenhagen"],
        "Krakow": ["Helsinki", "Warsaw", "Copenhagen", "Paris", "Oslo"]
    }
    
    total_days = 25
    days = list(range(1, total_days + 1))
    
    # Create Z3 variables
    day_vars = [Int(f"day_{i}") for i in days]
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day must be a valid city
    for d in day_vars:
        s.add(Or([d == city_ids[city] for city in cities]))
    
    # Total days per city
    for city, days_needed in cities.items():
        s.add(Sum([If(day_vars[i] == city_ids[city], 1, 0) for i in range(total_days)]) == days_needed)
    
    # Fixed events
    # Wedding in Riga on day 23 or 24
    s.add(Or(day_vars[22] == city_ids["Riga"], day_vars[23] == city_ids["Riga"]))
    
    # Workshop in Krakow on day 17 or 18
    s.add(Or(day_vars[16] == city_ids["Krakow"], day_vars[17] == city_ids["Krakow"]))
    
    # Meet friends in Paris between day 4-8
    s.add(Or([day_vars[i] == city_ids["Paris"] for i in range(3, 8)]))
    
    # Meet friend in Helsinki between day 18-22
    s.add(Or([day_vars[i] == city_ids["Helsinki"] for i in range(17, 22)]))
    
    # Visit relatives in Santorini on day 12 or 13
    s.add(Or(day_vars[11] == city_ids["Santorini"], day_vars[12] == city_ids["Santorini"]))
    
    # Flight connections between consecutive days
    for i in range(total_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            *[And(current == city_ids[city], next_day == city_ids[dest]) 
              for city in flights for dest in flights[city]]
        ))
    
    # Try to find a solution with a timeout
    s.set("timeout", 10000)  # 10 seconds
    if s.check() == sat:
        model = s.model()
        schedule = [id_to_city[model[day_vars[i]].as_long()] for i in range(total_days)]
        
        # Build itinerary
        itinerary = []
        current = schedule[0]
        start = 1
        for day in range(1, total_days + 1):
            if day == 1:
                continue
            if schedule[day - 1] != current:
                # Add stay
                if start == day - 1:
                    itinerary.append({"day_range": f"Day {start}", "place": current})
                else:
                    itinerary.append({"day_range": f"Day {start}-{day - 1}", "place": current})
                # Add flight
                itinerary.append({"day_range": f"Day {day}", "place": current})
                itinerary.append({"day_range": f"Day {day}", "place": schedule[day - 1]})
                current = schedule[day - 1]
                start = day
        # Add last stay
        if start == total_days:
            itinerary.append({"day_range": f"Day {start}", "place": current})
        else:
            itinerary.append({"day_range": f"Day {start}-{total_days}", "place": current})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found within time limit"}

print(json.dumps(solve_itinerary(), indent=2))