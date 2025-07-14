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
    
    # Direct flights as a dictionary: key is source, value is list of destinations
    direct_flights = {
        "Warsaw": ["Reykjavik", "Riga", "London", "Madrid", "Oslo"],
        "Oslo": ["Madrid", "Dubrovnik", "Reykjavik", "Riga", "Lyon", "London"],
        "Riga": ["Warsaw", "Oslo"],
        "Lyon": ["London", "Madrid"],
        "Madrid": ["London", "Lyon", "Oslo", "Dubrovnik"],
        "Dubrovnik": ["Madrid", "Oslo"],
        "London": ["Lyon", "Madrid", "Warsaw", "Reykjavik", "Oslo"],
        "Reykjavik": ["Warsaw", "Madrid", "London", "Oslo"]
    }
    
    # Total days
    total_days = 18
    
    # Create a solver instance
    s = Solver()
    
    # Create a list of days (1..18)
    days = range(1, total_days + 1)
    
    # For each day, which city are we in?
    day_city = [Int(f"day_{day}_city") for day in days]
    
    # Create a mapping from city names to integers
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraints: each day_city variable must be a valid city ID
    for dc in day_city:
        s.add(And(dc >= 0, dc < len(cities)))
    
    # Constraints for the number of days in each city
    for city, required_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day_city[day] == city_id, 1, 0) for day in range(total_days)]) == required_days)
    
    # Constraints for valid transitions between cities
    for day in range(total_days - 1):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # Either stay in the same city or take a direct flight
        s.add(Or(
            current_city == next_city,
            # There's a direct flight from current_city to next_city
            *[And(current_city == city_ids[src], next_city == city_ids[dst])
              for src in direct_flights for dst in direct_flights[src]
        ))
    
    # Special constraints:
    # 1. Wedding in Dubrovnik between day 7 and 8: so Dubrovnik must include day 7 or 8.
    s.add(Or(
        day_city[6] == city_ids["Dubrovnik"],  # day 7
        day_city[7] == city_ids["Dubrovnik"]   # day 8
    ))
    
    # 2. Meet friend in Riga between day 4 and 5: so Riga must include day 4 or 5.
    s.add(Or(
        day_city[3] == city_ids["Riga"],  # day 4
        day_city[4] == city_ids["Riga"]   # day 5
    ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Extract the sequence of cities per day
        sequence = []
        for day in range(total_days):
            city_id = m.evaluate(day_city[day]).as_long()
            sequence.append(id_to_city[city_id])
        
        # Build the itinerary
        itinerary = []
        current_city = sequence[0]
        start_day = 1
        
        for day in range(1, total_days):
            if sequence[day] != sequence[day - 1]:
                # Flight occurs on day (since day is 1-based, the flight is from day to day+1?)
                # Wait, no. The change happens between day-1 and day (0-based).
                # So in 1-based terms, between day and day+1.
                # So the stay in current_city is from start_day to day (1-based).
                if start_day == day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
                # The flight is on day (1-based), so add departure and arrival
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": sequence[day]})
                current_city = sequence[day]
                start_day = day + 1
        
        # Add the last stay
        if start_day <= total_days:
            if start_day == total_days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)