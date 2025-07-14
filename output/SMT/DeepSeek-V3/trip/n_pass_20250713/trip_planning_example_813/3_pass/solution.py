from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Seville": 5,
        "Vilnius": 3,
        "Santorini": 2,
        "London": 2,
        "Stuttgart": 3,
        "Dublin": 3,
        "Frankfurt": 5
    }
    
    # Direct flights as adjacency list
    flights = {
        "Frankfurt": ["Dublin", "London", "Vilnius", "Stuttgart"],
        "Dublin": ["Frankfurt", "London", "Seville", "Santorini"],
        "London": ["Frankfurt", "Dublin", "Santorini", "Stuttgart"],
        "Vilnius": ["Frankfurt"],
        "Stuttgart": ["Frankfurt", "London"],
        "Santorini": ["London", "Dublin"],
        "Seville": ["Dublin"]
    }
    
    # List of all cities
    city_list = list(cities.keys())
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Variables: day[i] is the city visited on day i (1-based)
    days = [Int(f"day_{i}") for i in range(1, 18)]  # Days 1 to 17
    
    # Each day's variable must be an index representing a city (0 to 6)
    for i in range(17):
        s.add(And(days[i] >= 0, days[i] < len(city_list)))
    
    # Constraint: total days per city
    for city_idx, city in enumerate(city_list):
        total_days = sum([If(days[i] == city_idx, 1, 0) for i in range(17)])
        s.add(total_days == cities[city])
    
    # Constraint: consecutive days in different cities must have a direct flight
    for i in range(16):  # days 1..16, checking i and i+1
        current_city = days[i]
        next_city = days[i+1]
        # If cities are different, check flight connection
        s.add(Implies(current_city != next_city, 
                      Or([And(current_city == city_list.index(a), next_city == city_list.index(b))
                          for a in flights for b in flights[a]])))
    
    # Specific constraints:
    # London on days 9 and 10
    london_idx = city_list.index("London")
    s.add(days[8] == london_idx)  # Day 9
    s.add(days[9] == london_idx)  # Day 10
    
    # Stuttgart on days 7, 8, and 9
    stuttgart_idx = city_list.index("Stuttgart")
    s.add(days[6] == stuttgart_idx)  # Day 7
    s.add(days[7] == stuttgart_idx)  # Day 8
    s.add(days[8] == stuttgart_idx)  # Day 9
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        day_assignments = []
        for i in range(17):
            day = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = city_list[city_idx]
            day_assignments.append((day, city))
        
        # Process day_assignments to create the itinerary with flight days
        current_place = day_assignments[0][1]
        start_day = 1
        for i in range(1, 17):
            day, city = day_assignments[i]
            if city != current_place:
                # Add the stay until previous day
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_place})
                # Add the flight day (both departure and arrival)
                itinerary.append({"day_range": f"Day {day}", "place": current_place})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_place = city
                start_day = day
            # else continue the stay
        # Add the last stay
        if start_day == 17:
            itinerary.append({"day_range": f"Day {17}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{17}", "place": current_place})
        
        # Prepare the output
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver
result = solve_itinerary()
print(json.dumps(result, indent=2))