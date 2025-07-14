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
    
    # Direct flights as tuples (source, destination)
    flights = [
        ("Warsaw", "Reykjavik"),
        ("Warsaw", "Riga"),
        ("Warsaw", "London"),
        ("Warsaw", "Madrid"),
        ("Warsaw", "Oslo"),
        ("Oslo", "Madrid"),
        ("Oslo", "Dubrovnik"),
        ("Oslo", "Reykjavik"),
        ("Oslo", "Riga"),
        ("Oslo", "Lyon"),
        ("Oslo", "London"),
        ("Riga", "Warsaw"),
        ("Riga", "Oslo"),
        ("Lyon", "London"),
        ("Lyon", "Madrid"),
        ("Madrid", "London"),
        ("Madrid", "Lyon"),
        ("Madrid", "Oslo"),
        ("Madrid", "Dubrovnik"),
        ("Dubrovnik", "Madrid"),
        ("Dubrovnik", "Oslo"),
        ("London", "Lyon"),
        ("London", "Madrid"),
        ("London", "Warsaw"),
        ("London", "Reykjavik"),
        ("London", "Oslo"),
        ("Reykjavik", "Warsaw"),
        ("Reykjavik", "Madrid"),
        ("Reykjavik", "London"),
        ("Reykjavik", "Oslo")
    ]
    
    # Total days
    total_days = 18
    
    # Create solver
    s = Solver()
    
    # Create day variables
    day_city = [Int(f"day_{day}") for day in range(1, total_days+1)]
    
    # City IDs
    city_ids = {city: i for i, city in enumerate(cities)}
    id_to_city = {i: city for city, i in city_ids.items()}
    
    # Each day must be a valid city
    for dc in day_city:
        s.add(And(dc >= 0, dc < len(cities)))
    
    # Count days in each city
    for city, days_needed in cities.items():
        s.add(Sum([If(dc == city_ids[city], 1, 0) for dc in day_city]) == days_needed)
    
    # Flight constraints
    for i in range(total_days-1):
        current = day_city[i]
        next_day = day_city[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            # Or take a direct flight
            *[And(current == city_ids[src], next_day == city_ids[dst]) 
              for (src, dst) in flights]
        ))
    
    # Special constraints
    # Wedding in Dubrovnik between day 7-8
    s.add(Or(
        day_city[6] == city_ids["Dubrovnik"],  # Day 7
        day_city[7] == city_ids["Dubrovnik"]   # Day 8
    ))
    
    # Meet friend in Riga between day 4-5
    s.add(Or(
        day_city[3] == city_ids["Riga"],  # Day 4
        day_city[4] == city_ids["Riga"]   # Day 5
    ))
    
    if s.check() == sat:
        m = s.model()
        sequence = [id_to_city[m.evaluate(dc).as_long()] for dc in day_city]
        
        # Build itinerary
        itinerary = []
        current = sequence[0]
        start = 1
        
        for day in range(1, total_days):
            if sequence[day] != sequence[day-1]:
                # Add stay
                if start == day:
                    itinerary.append({"day_range": f"Day {start}", "place": current})
                else:
                    itinerary.append({"day_range": f"Day {start}-{day}", "place": current})
                # Add flight
                itinerary.append({"day_range": f"Day {day}", "place": current})
                itinerary.append({"day_range": f"Day {day}", "place": sequence[day]})
                current = sequence[day]
                start = day + 1
        
        # Add final stay
        if start <= total_days:
            if start == total_days:
                itinerary.append({"day_range": f"Day {start}", "place": current})
            else:
                itinerary.append({"day_range": f"Day {start}-{total_days}", "place": current})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate itinerary
itinerary = solve_itinerary()
print(itinerary)