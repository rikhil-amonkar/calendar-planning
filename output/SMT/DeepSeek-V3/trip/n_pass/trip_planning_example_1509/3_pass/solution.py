from z3 import *
import json

def solve_itinerary():
    # Cities to visit with their required days
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
    
    # Direct flights: adjacency list
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
    
    # Total days
    total_days = 25
    days = list(range(1, total_days + 1))
    
    # Create Z3 variables: day[i] is the city on day i (1-based)
    day_vars = [Int(f"day_{i}") for i in days]
    
    # Create a mapping from city names to integers
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Solver instance
    s = Solver()
    
    # Each day_vars[i] must be a valid city id
    for d in day_vars:
        s.add(Or([d == city_ids[city] for city in cities]))
    
    # Constraints for total days in each city
    for city, required_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day_vars[i] == city_id, 1, 0) for i in range(total_days)]) == required_days)
    
    # Constraints for specific events:
    # Paris between day 4 and 8 (meet friends)
    s.add(Or([day_vars[i] == city_ids["Paris"] for i in range(3, 8)]))  # days 4-8 (1-based: indices 3-7)
    
    # Workshop in Krakow between day 17 and 18
    s.add(Or(day_vars[16] == city_ids["Krakow"], day_vars[17] == city_ids["Krakow"]))
    
    # Wedding in Riga between day 23 and 24
    s.add(Or(day_vars[22] == city_ids["Riga"], day_vars[23] == city_ids["Riga"]))
    
    # Meet friend in Helsinki between day 18 and 22
    s.add(Or([day_vars[i] == city_ids["Helsinki"] for i in range(17, 22)]))
    
    # Visit relatives in Santorini between day 12 and 13
    s.add(Or(day_vars[11] == city_ids["Santorini"], day_vars[12] == city_ids["Santorini"]))
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(total_days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_ids[city], next_city == city_ids[adj]) 
              for city in flights for adj in flights[city] if adj in city_ids]
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Decode the model into a list of cities per day
        schedule = [id_to_city[model[day_vars[i]].as_long()] for i in range(total_days)]
        
        # Generate the itinerary in the required format
        current_place = schedule[0]
        start_day = 1
        for day in range(1, total_days + 1):
            if day == 1:
                continue
            if schedule[day - 1] != current_place:
                # Add the stay up to the previous day
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_place})
                # Add the flight day entries
                itinerary.append({"day_range": f"Day {day}", "place": current_place})
                itinerary.append({"day_range": f"Day {day}", "place": schedule[day - 1]})
                current_place = schedule[day - 1]
                start_day = day
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_place})
        
        # Verify that all cities are visited for the required days
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start, end = map(int, day_range.replace("Day ", "").split('-'))
                duration = end - start + 1
            else:
                duration = 1
            city_days[place] += duration
        
        # Check against required days
        for city, required in cities.items():
            assert city_days[city] == required, f"{city} has {city_days[city]} days, expected {required}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))