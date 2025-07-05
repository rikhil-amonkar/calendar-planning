import json
from z3 import *

def solve_scheduling_problem():
    # Define the cities and their required stay durations
    cities = {
        "Warsaw": 4,
        "Venice": 3,
        "Vilnius": 3,
        "Salzburg": 4,
        "Amsterdam": 2,
        "Barcelona": 5,
        "Paris": 2,
        "Hamburg": 4,
        "Florence": 5,
        "Tallinn": 2
    }
    
    # Define the direct flight connections
    direct_flights = {
        "Paris": ["Venice", "Hamburg", "Vilnius", "Amsterdam", "Florence", "Warsaw", "Tallinn", "Barcelona"],
        "Barcelona": ["Amsterdam", "Warsaw", "Hamburg", "Florence", "Venice", "Tallinn"],
        "Amsterdam": ["Warsaw", "Vilnius", "Hamburg", "Florence", "Venice", "Tallinn"],
        "Warsaw": ["Venice", "Vilnius", "Hamburg", "Tallinn"],
        "Venice": ["Hamburg"],
        "Vilnius": ["Tallinn"],
        "Hamburg": ["Salzburg"],
        "Tallinn": ["Vilnius"],
        "Florence": [],
        "Salzburg": []
    }
    
    # Expand the flight connections to be bidirectional
    flight_connections = {}
    for city in cities:
        flight_connections[city] = set()
    
    # Populate the flight connections
    connections = [
        ("Paris", "Venice"), ("Paris", "Hamburg"), ("Paris", "Vilnius"), ("Paris", "Amsterdam"), 
        ("Paris", "Florence"), ("Paris", "Warsaw"), ("Paris", "Tallinn"), ("Paris", "Barcelona"),
        ("Barcelona", "Amsterdam"), ("Barcelona", "Warsaw"), ("Barcelona", "Hamburg"), 
        ("Barcelona", "Florence"), ("Barcelona", "Venice"), ("Barcelona", "Tallinn"),
        ("Amsterdam", "Warsaw"), ("Amsterdam", "Vilnius"), ("Amsterdam", "Hamburg"), 
        ("Amsterdam", "Florence"), ("Amsterdam", "Venice"), ("Amsterdam", "Tallinn"),
        ("Warsaw", "Venice"), ("Warsaw", "Vilnius"), ("Warsaw", "Hamburg"), ("Warsaw", "Tallinn"),
        ("Venice", "Hamburg"), ("Vilnius", "Tallinn"), ("Hamburg", "Salzburg")
    ]
    
    for a, b in connections:
        flight_connections[a].add(b)
        flight_connections[b].add(a)
    
    # Total days
    total_days = 25
    
    # Create Z3 variables for each day's city
    day_city = [Int(f"day_{i}_city") for i in range(1, total_days + 1)]
    
    # Create a mapping from city names to integers
    city_to_int = {city: idx for idx, city in enumerate(cities.keys())}
    int_to_city = {idx: city for city, idx in city_to_int.items()}
    
    s = Solver()
    
    # Each day's city must be one of the 10 cities
    for day in day_city:
        s.add(Or([day == city_to_int[city] for city in cities]))
    
    # Constraints for stay durations
    for city in cities:
        total_stay = Sum([If(day == city_to_int[city], 1, 0) for day in day_city])
        s.add(total_stay == cities[city])
    
    # Date-specific constraints
    # Paris workshop between day 1 and day 2: must be in Paris on day 1 and day 2
    s.add(day_city[0] == city_to_int["Paris"])
    s.add(day_city[1] == city_to_int["Paris"])
    
    # Barcelona friends between day 2 and day 6 (days 3-7 in 1-based): at least some days in Barcelona in this range
    s.add(Or([day_city[i] == city_to_int["Barcelona"] for i in range(2, 6)]))
    
    # Tallinn friend between day 11 and 12 (days 12-13 in 1-based)
    s.add(Or(day_city[11] == city_to_int["Tallinn"], day_city[12] == city_to_int["Tallinn"]))
    
    # Hamburg conference between day 19 and 22 (days 20-23 in 1-based)
    for i in range(19, 22):
        s.add(day_city[i] == city_to_int["Hamburg"])
    
    # Salzburg wedding between day 22 and 25 (days 23-25 in 1-based)
    for i in range(22, 25):
        s.add(day_city[i] == city_to_int["Salzburg"])
    
    # Flight constraints: consecutive days must be either same city or connected by direct flight
    for i in range(total_days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_int[a], next_city == city_to_int[b]) 
              for a in cities for b in flight_connections[a] if b in cities]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        # Generate the day sequence from the model
        day_sequence = []
        for i in range(total_days):
            city_int = model.evaluate(day_city[i]).as_long()
            city = int_to_city[city_int]
            day_sequence.append(city)
        
        # Process the day sequence to create the itinerary with ranges
        i = 0
        while i < total_days:
            current_city = day_sequence[i]
            j = i
            while j < total_days and day_sequence[j] == current_city:
                j += 1
            stay_length = j - i
            if stay_length > 1:
                itinerary.append({
                    "day_range": f"Day {i + 1}-{j}",
                    "place": current_city
                })
            else:
                itinerary.append({
                    "day_range": f"Day {i + 1}",
                    "place": current_city
                })
            i = j
        
        # Handle flight days by duplicating entries where city changes
        refined_itinerary = []
        for i in range(len(itinerary)):
            entry = itinerary[i]
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start, end = map(int, day_range.replace("Day ", "").split('-'))
                refined_itinerary.append(entry)
                # Check if the next entry is a different place and starts right after
                if i < len(itinerary) - 1:
                    next_entry = itinerary[i + 1]
                    next_day_range = next_entry["day_range"]
                    next_place = next_entry["place"]
                    if next_place != place:
                        if "Day " in next_day_range and '-' not in next_day_range:
                            next_day = int(next_day_range.replace("Day ", ""))
                            if next_day == end + 1:
                                # Add the departure day as a single day
                                refined_itinerary.append({
                                    "day_range": f"Day {end}",
                                    "place": place
                                })
                                refined_itinerary.append({
                                    "day_range": f"Day {next_day}",
                                    "place": next_place
                                })
            else:
                refined_itinerary.append(entry)
        
        # Post-process to ensure flight days are correctly represented
        final_itinerary = []
        i = 0
        while i < len(refined_itinerary):
            current = refined_itinerary[i]
            if i < len(refined_itinerary) - 1:
                next_entry = refined_itinerary[i + 1]
                # Check if current and next are single days with different places
                if '-' not in current["day_range"] and '-' not in next_entry["day_range"]:
                    current_day = int(current["day_range"].replace("Day ", ""))
                    next_day = int(next_entry["day_range"].replace("Day ", ""))
                    if current_day == next_day:
                        # Flight day: duplicate
                        final_itinerary.append(current)
                        final_itinerary.append(next_entry)
                        i += 2
                        continue
            final_itinerary.append(current)
            i += 1
        
        # Ensure all constraints are met in the final itinerary
        # Convert to the required JSON format
        output = {"itinerary": final_itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Generate the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))