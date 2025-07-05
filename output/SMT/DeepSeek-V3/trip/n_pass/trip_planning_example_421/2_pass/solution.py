from z3 import *
import json

def solve_itinerary():
    # Define the cities and their required days
    cities = {
        "Nice": 5,
        "Krakow": 6,
        "Dublin": 7,
        "Lyon": 4,
        "Frankfurt": 2
    }
    
    # Direct flights as adjacency list
    direct_flights = {
        "Nice": ["Dublin", "Frankfurt", "Lyon"],
        "Dublin": ["Nice", "Frankfurt", "Krakow", "Lyon"],
        "Krakow": ["Dublin", "Frankfurt"],
        "Lyon": ["Frankfurt", "Dublin", "Nice"],
        "Frankfurt": ["Dublin", "Krakow", "Lyon", "Nice"]
    }
    
    # Total days
    total_days = 20
    
    # Create a solver instance
    s = Solver()
    
    # Create variables for each day: day 1 to day 20
    day_vars = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    # Assign each day_var to a city (using enumerated constants)
    city_enum = {city: idx for idx, city in enumerate(cities.keys())}
    idx_to_city = {idx: city for city, idx in city_enum.items()}
    
    for day in day_vars:
        s.add(day >= 0, day < len(cities))
    
    # Constraint: Nice from day 1 to day 5
    for i in range(1, 6):
        s.add(day_vars[i-1] == city_enum["Nice"])
    
    # Constraint: Frankfurt on day 19 and 20
    s.add(day_vars[18] == city_enum["Frankfurt"])
    s.add(day_vars[19] == city_enum["Frankfurt"])
    
    # Constraint: Total days per city
    for city, days in cities.items():
        s.add(Sum([If(day == city_enum[city], 1, 0) for day in day_vars]) == days
    
    # Constraint: Flight connections between consecutive different cities
    for i in range(total_days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i+1]
        # If changing cities, ensure there's a direct flight
        s.add(Implies(current_day != next_day, 
                      Or([And(current_day == city_enum[city], next_day == city_enum[adj])
                          for city in direct_flights 
                          for adj in direct_flights[city]])))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Generate the day sequence from the model
        day_sequence = []
        for i in range(total_days):
            day_val = model.evaluate(day_vars[i]).as_long()
            day_sequence.append(idx_to_city[day_val])
        
        # Process the day sequence to create the itinerary
        current_place = day_sequence[0]
        start_day = 1
        for day in range(1, total_days):
            if day_sequence[day] != current_place:
                # Add the stay up to the previous day
                if start_day == day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_place})
                # Add the transition day (same day for both places)
                itinerary.append({"day_range": f"Day {day}", "place": current_place})
                itinerary.append({"day_range": f"Day {day}", "place": day_sequence[day]})
                current_place = day_sequence[day]
                start_day = day + 1
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_place})
        
        # Verify the total days per city
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start, end = map(int, day_range.replace("Day ", "").split('-'))
                days = end - start + 1
            else:
                days = 1
            city_days[place] += days
        
        # Check if the city days match the requirements
        for city, days in cities.items():
            assert city_days[city] == days, f"City {city} has {city_days[city]} days, expected {days}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))