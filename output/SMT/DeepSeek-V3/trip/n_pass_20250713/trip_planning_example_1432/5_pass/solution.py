from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ["Frankfurt", "Salzburg", "Athens", "Reykjavik", "Bucharest", 
              "Valencia", "Vienna", "Amsterdam", "Stockholm", "Riga"]
    
    # Direct flights as per the problem statement
    direct_flights = {
        "Valencia": ["Frankfurt", "Athens", "Bucharest", "Vienna", "Amsterdam"],
        "Vienna": ["Bucharest", "Riga", "Frankfurt", "Stockholm", "Amsterdam", "Athens", "Reykjavik", "Valencia"],
        "Athens": ["Valencia", "Bucharest", "Riga", "Stockholm", "Frankfurt", "Vienna", "Reykjavik", "Amsterdam"],
        "Riga": ["Frankfurt", "Bucharest", "Vienna", "Amsterdam", "Stockholm", "Athens"],
        "Stockholm": ["Athens", "Vienna", "Amsterdam", "Reykjavik", "Frankfurt", "Riga"],
        "Amsterdam": ["Bucharest", "Frankfurt", "Reykjavik", "Stockholm", "Valencia", "Vienna", "Riga", "Athens"],
        "Bucharest": ["Vienna", "Athens", "Amsterdam", "Frankfurt", "Valencia", "Riga"],
        "Frankfurt": ["Valencia", "Riga", "Amsterdam", "Salzburg", "Vienna", "Athens", "Bucharest", "Stockholm", "Reykjavik"],
        "Reykjavik": ["Amsterdam", "Frankfurt", "Athens", "Stockholm", "Vienna"],
        "Salzburg": ["Frankfurt"]
    }
    
    # Total days
    total_days = 29
    
    # Create a solver instance
    s = Solver()
    
    # Variables: for each day, which city are we in?
    # day_place[d] is the city we are in on day d+1 (since days are 1-based)
    day_place = [Int(f"day_{d+1}") for d in range(total_days)]
    
    # Assign each city to a unique integer
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Constraint: each day_place must be a valid city index
    for d in range(total_days):
        s.add(day_place[d] >= 0, day_place[d] < len(cities))
    
    # Constraint: consecutive days must be either the same city or connected by a direct flight
    for d in range(total_days - 1):
        current_city = day_place[d]
        next_city = day_place[d+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == city_to_int[src], next_city == city_to_int[dest]) 
                for src in cities for dest in direct_flights.get(src, [])])
        ))
    
    # Helper function to add stay constraints for a city between start_day and end_day (inclusive)
    def add_stay_constraint(city, start_day, end_day):
        for d in range(start_day - 1, end_day):
            s.add(day_place[d] == city_to_int[city])
    
    # Add constraints based on the problem statement
    # Stockholm: meet friend between day 1-3
    add_stay_constraint("Stockholm", 1, 3)
    
    # Valencia: attend show between day 5-6
    add_stay_constraint("Valencia", 5, 6)
    
    # Vienna: attend wedding between day 6-10
    add_stay_constraint("Vienna", 6, 10)
    
    # Athens: workshop between day 14-18
    add_stay_constraint("Athens", 14, 18)
    
    # Riga: conference between day 18-20
    add_stay_constraint("Riga", 18, 20)
    
    # Now, add constraints for the total days in each city
    city_days = {
        "Frankfurt": 4,
        "Salzburg": 5,
        "Athens": 5,
        "Reykjavik": 5,
        "Bucharest": 3,
        "Valencia": 2,
        "Vienna": 5,
        "Amsterdam": 3,
        "Stockholm": 3,
        "Riga": 3
    }
    
    # For each city, the sum of days where day_place equals the city must match city_days
    for city in cities:
        total = 0
        for d in range(total_days):
            total += If(day_place[d] == city_to_int[city], 1, 0)
        s.add(total == city_days[city])
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Extract the itinerary
        sequence = [m.evaluate(day_place[d]).as_long() for d in range(total_days)]
        city_sequence = [int_to_city[idx] for idx in sequence]
        
        itinerary = []
        current_city = city_sequence[0]
        start_day = 1
        for day in range(1, total_days + 1):
            if day == total_days or city_sequence[day - 1] != city_sequence[day % total_days]:
                end_day = day
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
                if day < total_days:
                    next_city = city_sequence[day]
                    itinerary.append({"day_range": f"Day {end_day}", "place": current_city})
                    itinerary.append({"day_range": f"Day {end_day}", "place": next_city})
                start_day = day + 1
                if day < total_days:
                    current_city = city_sequence[day]
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))