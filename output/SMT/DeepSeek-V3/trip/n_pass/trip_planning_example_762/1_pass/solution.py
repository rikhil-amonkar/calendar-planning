from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
    
    # Direct flights as per the problem description
    direct_flights = {
        'London': ['Madrid', 'Oslo', 'Dublin', 'Berlin'],
        'Madrid': ['London', 'Oslo', 'Dublin', 'Berlin'],
        'Oslo': ['London', 'Madrid', 'Vilnius', 'Berlin', 'Dublin'],
        'Dublin': ['Madrid', 'Oslo', 'London', 'Berlin'],
        'Vilnius': ['Oslo', 'Berlin'],
        'Berlin': ['Madrid', 'Vilnius', 'Oslo', 'London', 'Dublin']
    }
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Variables: for each day (1..13), which city are we in?
    day_city = [Int(f"day_{i}_city") for i in range(1, 14)]  # Days 1 to 13
    
    # Map each city to an integer
    city_map = {city: idx for idx, city in enumerate(cities)}
    city_inv_map = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints: each day_city must be between 0 and 5 (inclusive)
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # Constraints for the number of days in each city
    # Dublin: 3 days
    s.add(Sum([If(day_city[i] == city_map['Dublin'], 1, 0) for i in range(13)]) == 3)
    # Madrid: 2 days
    s.add(Sum([If(day_city[i] == city_map['Madrid'], 1, 0) for i in range(13)]) == 2)
    # Oslo: 3 days
    s.add(Sum([If(day_city[i] == city_map['Oslo'], 1, 0) for i in range(13)]) == 3)
    # London: 2 days
    s.add(Sum([If(day_city[i] == city_map['London'], 1, 0) for i in range(13)]) == 2)
    # Vilnius: 3 days
    s.add(Sum([If(day_city[i] == city_map['Vilnius'], 1, 0) for i in range(13)]) == 3)
    # Berlin: 5 days
    s.add(Sum([If(day_city[i] == city_map['Berlin'], 1, 0) for i in range(13)]) == 5)
    
    # Specific day constraints:
    # Dublin between day 7 and day 9 (inclusive) for meeting friends.
    # So at least one of days 7,8,9 must be in Dublin.
    s.add(Or(
        day_city[6] == city_map['Dublin'],  # Day 7 is index 6
        day_city[7] == city_map['Dublin'],   # Day 8
        day_city[8] == city_map['Dublin']    # Day 9
    ))
    
    # Madrid between day 2 and day 3 (inclusive) for visiting relatives.
    s.add(Or(
        day_city[1] == city_map['Madrid'],  # Day 2
        day_city[2] == city_map['Madrid']   # Day 3
    ))
    
    # Berlin between day 3 and day 7 (inclusive) for wedding.
    s.add(Or([day_city[i] == city_map['Berlin'] for i in range(2, 7)]))  # Days 3-7 (indices 2-6)
    
    # Flight constraints: consecutive days can only change to directly connected cities
    for i in range(12):  # Days 1..12 to 2..13
        current_city = day_city[i]
        next_city = day_city[i+1]
        # Either stay in the same city, or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == city_map[dep], next_city == city_map[arr])
                for dep in direct_flights
                for arr in direct_flights[dep]])
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Determine the stay ranges
        current_city = None
        start_day = 1
        for day in range(1, 14):
            city_idx = m.evaluate(day_city[day-1]).as_long()
            city = city_inv_map[city_idx]
            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                # Add the stay for the previous city
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_city})
                # Add the flight day entries for both cities
                itinerary.append({"day_range": f"Day {day-1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day-1}", "place": city})
                current_city = city
                start_day = day
        # Add the last stay
        if start_day == 13:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-13", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found."}

# Solve and print the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))