from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3
    }
    
    # Direct flights
    direct_flights = {
        "Warsaw": ["Reykjavik", "Riga", "London", "Madrid", "Oslo"],
        "Oslo": ["Madrid", "Warsaw", "Dubrovnik", "Reykjavik", "Riga", "Lyon", "London"],
        "Riga": ["Warsaw", "Oslo"],
        "Lyon": ["London", "Madrid", "Oslo"],
        "Madrid": ["Oslo", "London", "Lyon", "Dubrovnik", "Warsaw"],
        "Dubrovnik": ["Oslo", "Madrid"],
        "London": ["Lyon", "Madrid", "Warsaw", "Oslo", "Reykjavik"],
        "Reykjavik": ["Warsaw", "Oslo", "London", "Madrid"]
    }
    
    total_days = 18
    
    # Create a list of days 1..18, each day is assigned to a city
    day_assignments = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day is assigned to a valid city
    for day in day_assignments:
        s.add(day >= 0, day < len(cities))
    
    # Count of days per city matches the requirements
    for city, days_needed in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day == city_id, 1, 0) for day in day_assignments]) == days_needed)
    
    # Riga constraint: day 4 or 5 is Riga
    s.add(Or(day_assignments[3] == city_ids["Riga"], day_assignments[4] == city_ids["Riga"]))
    
    # Dubrovnik constraint: day 7 or 8 is Dubrovnik
    s.add(Or(day_assignments[6] == city_ids["Dubrovnik"], day_assignments[7] == city_ids["Dubrovnik"]))
    
    # Flight constraints: consecutive different cities must have a direct flight
    for i in range(total_days - 1):
        current_day = day_assignments[i]
        next_day = day_assignments[i + 1]
        s.add(Implies(current_day != next_day,
                      Or([And(current_day == city_ids[c1], next_day == city_ids[c2])
                          for c1 in direct_flights for c2 in direct_flights[c1]])))
    
    if s.check() == sat:
        m = s.model()
        assigned_days = [id_to_city[m.evaluate(day).as_long()] for day in day_assignments]
        
        itinerary = []
        current_city = assigned_days[0]
        start_day = 1
        
        for day in range(1, total_days):
            if assigned_days[day] != current_city:
                end_day = day
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_range, "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": assigned_days[day]})
                current_city = assigned_days[day]
                start_day = day + 1
        
        # Add the last segment
        end_day = total_days
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))