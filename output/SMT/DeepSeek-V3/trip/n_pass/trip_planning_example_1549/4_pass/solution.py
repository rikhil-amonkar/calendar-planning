from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
    days_total = 28
    
    # Direct flights as per the problem description
    direct_flights = {
        "Riga": ["Prague", "Milan", "Tallinn", "Warsaw", "Stockholm"],
        "Stockholm": ["Milan", "Lisbon", "Santorini", "Warsaw", "Prague", "Tallinn", "Riga"],
        "Milan": ["Stockholm", "Riga", "Naples", "Porto", "Prague", "Lisbon", "Santorini", "Warsaw"],
        "Lisbon": ["Stockholm", "Warsaw", "Naples", "Porto", "Prague", "Riga", "Milan"],
        "Naples": ["Warsaw", "Milan", "Lisbon", "Santorini"],
        "Warsaw": ["Naples", "Lisbon", "Stockholm", "Riga", "Tallinn", "Porto", "Milan", "Prague"],
        "Porto": ["Lisbon", "Milan", "Warsaw"],
        "Prague": ["Riga", "Tallinn", "Stockholm", "Lisbon", "Milan", "Warsaw"],
        "Tallinn": ["Riga", "Prague", "Stockholm", "Warsaw"],
        "Santorini": ["Stockholm", "Milan", "Naples"]
    }
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Create variables: for each day, which city are we in?
    day_to_city = [Int(f"day_{i}_city") for i in range(1, days_total + 1)]
    
    # Assign each city a unique integer
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints that each day's variable is within 0..9 (indices of cities)
    for day_var in day_to_city:
        s.add(day_var >= 0, day_var < len(cities))
    
    # Constraints for the number of days in each city
    required_days = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2
    }
    
    # Count the occurrences of each city in the day assignments
    for city in cities:
        count = 0
        for day_var in day_to_city:
            count += If(day_var == city_to_int[city], 1, 0)
        s.add(count == required_days[city])
    
    # Special constraints:
    # Riga must be visited from day 5 to day 8 (inclusive)
    for day in range(5, 9):
        s.add(day_to_city[day - 1] == city_to_int["Riga"])
    
    # Tallinn must be visited between day 18 and 20 (inclusive)
    tallinn_constraint = Or([day_to_city[day - 1] == city_to_int["Tallinn"] for day in range(18, 21)])
    s.add(tallinn_constraint)
    
    # Milan must be visited between day 24 and 26 (inclusive)
    milan_constraint = Or([day_to_city[day - 1] == city_to_int["Milan"] for day in range(24, 27)])
    s.add(milan_constraint)
    
    # Flight constraints: consecutive days must be either the same city or have a direct flight
    for i in range(days_total - 1):
        current_day_var = day_to_city[i]
        next_day_var = day_to_city[i + 1]
        # Either stay in the same city or move to a directly connected city
        same_city = (current_day_var == next_day_var)
        # Create a condition for each possible current city and its direct flights
        flight_possibilities = []
        for city in cities:
            current_city_int = city_to_int[city]
            # If current day is city, then next day must be city or in its direct flights
            possible_targets = direct_flights[city] + [city]
            target_ints = [city_to_int[c] for c in possible_targets]
            flight_possibilities.append(And(current_day_var == current_city_int, Or([next_day_var == target_int for target_int in target_ints])))
        s.add(Or(same_city, Or(flight_possibilities)))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Build the itinerary
        itinerary = []
        current_city = None
        start_day = 1
        for day in range(1, days_total + 1):
            city_idx = m.evaluate(day_to_city[day - 1]).as_long()
            city = int_to_city[city_idx]
            if day == 1:
                current_city = city
                start_day = 1
            else:
                prev_city_idx = m.evaluate(day_to_city[day - 2]).as_long()
                prev_city = int_to_city[prev_city_idx]
                if city != prev_city:
                    # Flight day: day is spent in both cities
                    if start_day < day:
                        itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day}", "place": city})
                    start_day = day + 1
                    current_city = city
        # Add the last segment
        if start_day <= days_total:
            if start_day == days_total:
                itinerary.append({"day_range": f"Day {days_total}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{days_total}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))