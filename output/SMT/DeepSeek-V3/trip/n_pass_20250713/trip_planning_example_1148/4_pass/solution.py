from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Lisbon": 2,
        "Dubrovnik": 5,
        "Copenhagen": 5,
        "Prague": 3,
        "Tallinn": 2,
        "Stockholm": 4,
        "Split": 3,
        "Lyon": 2
    }
    
    # Direct flights
    direct_flights = {
        "Dubrovnik": ["Stockholm", "Copenhagen"],
        "Lisbon": ["Copenhagen", "Lyon", "Stockholm", "Prague"],
        "Copenhagen": ["Lisbon", "Stockholm", "Split", "Dubrovnik", "Prague", "Tallinn"],
        "Prague": ["Stockholm", "Lisbon", "Lyon", "Copenhagen", "Split"],
        "Tallinn": ["Stockholm", "Copenhagen", "Prague"],
        "Stockholm": ["Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Lisbon", "Split"],
        "Split": ["Copenhagen", "Stockholm", "Prague", "Lyon"],
        "Lyon": ["Lisbon", "Prague", "Split"]
    }
    
    # Fixed events
    fixed_events = [
        ("Tallinn", 1, 2),  # Meet friend between day 1-2
        ("Lisbon", 4, 5),   # Workshop between day 4-5
        ("Stockholm", 13, 16),  # Wedding between day 13-16
        ("Lyon", 18, 19)    # Annual show between day 18-19
    ]
    
    # Create Z3 variables
    day_to_city = {day: Int(f"day_{day}") for day in range(1, 20)}  # Days 1 to 19
    
    # City encodings (assign each city a unique integer)
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Constraints: each day's city must be a valid city ID
    for day in range(1, 20):
        s.add(Or([day_to_city[day] == city_ids[city] for city in cities]))
    
    # Constraints for fixed events
    for city, start_day, end_day in fixed_events:
        for day in range(start_day, end_day + 1):
            s.add(day_to_city[day] == city_ids[city])
    
    # Flight constraints: consecutive days can only change to directly connected cities
    for day in range(1, 19):
        current_city_var = day_to_city[day]
        next_city_var = day_to_city[day + 1]
        # Either stay in the same city or fly to a directly connected city
        s.add(Or(
            current_city_var == next_city_var,
            *[
                And(current_city_var == city_ids[city], next_city_var == city_ids[neighbor])
                for city in cities
                for neighbor in direct_flights.get(city, [])
            ]
        ))
    
    # Constraints for total days in each city
    for city in cities:
        total_days = cities[city]
        s.add(Sum([If(day_to_city[day] == city_ids[city], 1, 0) for day in range(1, 20)]) == total_days
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary_days = []
        for day in range(1, 20):
            city_id = model.evaluate(day_to_city[day]).as_long()
            itinerary_days.append(id_to_city[city_id])
        
        # Generate the itinerary in the required format
        itinerary = []
        current_place = itinerary_days[0]
        start_day = 1
        
        for day in range(2, 20):
            if itinerary_days[day - 1] != current_place:
                # Add the stay up to the previous day
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_place})
                # Add the flight day records
                itinerary.append({"day_range": f"Day {day}", "place": current_place})
                itinerary.append({"day_range": f"Day {day}", "place": itinerary_days[day - 1]})
                current_place = itinerary_days[day - 1]
                start_day = day
        # Add the last stay
        if start_day == 19:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-19", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found."}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))