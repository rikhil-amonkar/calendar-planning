from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Rome": 3,
        "Mykonos": 2,
        "Lisbon": 2,
        "Frankfurt": 5,
        "Nice": 3,
        "Stuttgart": 4,
        "Venice": 4,
        "Dublin": 2,
        "Bucharest": 2,
        "Seville": 5
    }
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("Rome", "Stuttgart"),
        ("Rome", "Venice"),
        ("Rome", "Mykonos"),
        ("Rome", "Seville"),
        ("Rome", "Frankfurt"),
        ("Rome", "Bucharest"),
        ("Rome", "Dublin"),
        ("Rome", "Lisbon"),
        ("Rome", "Nice"),
        ("Mykonos", "Nice"),
        ("Lisbon", "Seville"),
        ("Lisbon", "Bucharest"),
        ("Lisbon", "Venice"),
        ("Lisbon", "Dublin"),
        ("Lisbon", "Rome"),
        ("Lisbon", "Frankfurt"),
        ("Lisbon", "Nice"),
        ("Lisbon", "Stuttgart"),
        ("Frankfurt", "Venice"),
        ("Frankfurt", "Rome"),
        ("Frankfurt", "Dublin"),
        ("Frankfurt", "Nice"),
        ("Frankfurt", "Stuttgart"),
        ("Frankfurt", "Bucharest"),
        ("Frankfurt", "Lisbon"),
        ("Nice", "Dublin"),
        ("Nice", "Venice"),
        ("Nice", "Rome"),
        ("Nice", "Lisbon"),
        ("Nice", "Frankfurt"),
        ("Stuttgart", "Venice"),
        ("Stuttgart", "Frankfurt"),
        ("Stuttgart", "Lisbon"),
        ("Venice", "Dublin"),
        ("Venice", "Lisbon"),
        ("Dublin", "Bucharest"),
        ("Dublin", "Seville"),
        ("Bucharest", "Lisbon"),
        ("Seville", "Dublin")
    ]
    
    # Make sure all flights are bidirectional
    all_flights = set()
    for a, b in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    # Fixed events
    wedding_start, wedding_end = 1, 5  # Frankfurt
    conference_start, conference_end = 13, 17  # Seville
    mykonos_meet_start, mykonos_meet_end = 10, 11  # Mykonos
    
    total_days = 23
    days = list(range(1, total_days + 1))
    
    # Create Z3 variables: day -> city
    city_vars = {day: Int(f'day_{day}') for day in days}
    
    # City encodings
    city_ids = {city: idx for idx, city in enumerate(cities.keys(), 1)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day must be assigned a valid city
    for day in days:
        s.add(Or([city_vars[day] == city_ids[city] for city in cities]))
    
    # Frankfurt must be between day 1-5 (wedding)
    for day in range(wedding_start, wedding_end + 1):
        s.add(city_vars[day] == city_ids["Frankfurt"])
    
    # Seville must be between day 13-17 (conference)
    for day in range(conference_start, conference_end + 1):
        s.add(city_vars[day] == city_ids["Seville"])
    
    # Mykonos must include day 10 or 11 (meet friends)
    s.add(Or(city_vars[10] == city_ids["Mykonos"], city_vars[11] == city_ids["Mykonos"]))
    
    # Ensure the required days per city
    for city, req_days in cities.items():
        total = 0
        for day in days:
            total += If(city_vars[day] == city_ids[city], 1, 0)
        s.add(total == req_days)
    
    # Flight transitions: consecutive days must be same city or have a direct flight
    for i in range(1, total_days):
        current_city_var = city_vars[i]
        next_city_var = city_vars[i+1]
        # Either stay in the same city or fly to a directly connected city
        same_city = current_city_var == next_city_var
        possible_flights = []
        for city1 in cities:
            for city2 in cities:
                if (city1, city2) in all_flights:
                    possible_flights.append(And(current_city_var == city_ids[city1], next_city_var == city_ids[city2]))
        s.add(Or(same_city, Or(possible_flights)))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        current_city = None
        start_day = 1
        for day in days:
            city_id = model.evaluate(city_vars[day]).as_long()
            city = id_to_city[city_id]
            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                # Add the previous stay
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                # Add the transition day (flight)
                itinerary.append({"day_range": f"Day {day - 1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_city = city
                start_day = day
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))