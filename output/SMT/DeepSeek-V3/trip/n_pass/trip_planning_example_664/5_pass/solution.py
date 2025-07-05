from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2
    }
    
    # Direct flights as a dictionary for easy lookup
    direct_flights = {
        "Milan": ["Stockholm", "Munich", "Seville"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Munich": ["Stockholm", "Bucharest", "Seville", "Milan", "Tallinn"],
        "Bucharest": ["Munich"],
        "Seville": ["Munich", "Milan"],
        "Tallinn": ["Stockholm", "Munich"]
    }
    
    # Days are 1..18
    days = 18
    
    # Create a solver instance
    s = Solver()
    
    # Variables: for each day, which city are we in?
    # day_city[d] is the city index for day d
    day_city = [Int(f"day_{day}_city") for day in range(1, days+1)]
    for dc in day_city:
        s.add(dc >= 0, dc < len(cities))
    
    # Flight variables: flight_taken[d] is true if we fly on day d
    flight_taken = [Bool(f"flight_{day}") for day in range(1, days)]
    
    # Constraints
    
    # 1. No flights on consecutive days
    for day in range(1, days-1):
        s.add(Not(And(flight_taken[day-1], flight_taken[day])))
    
    # 2. Flight constraints
    for day in range(1, days):
        # If we fly on day d, then:
        # day d and d+1 must be different cities
        # and there must be a direct flight between them
        s.add(Implies(flight_taken[day-1],
                     And(day_city[day-1] != day_city[day],
                         Or([And(day_city[day-1] == i, day_city[day] == j)
                            for i, city1 in enumerate(cities)
                            for j, city2 in enumerate(cities)
                            if city2 in direct_flights[city1]])))
    
    # 3. Duration constraints
    # Tallinn: 2 days
    s.add(Sum([If(day_city[day] == list(cities.keys()).index("Tallinn"), 1, 0) 
               for day in range(days)]) == 2)
    # Bucharest: 4 days between day 1-4
    s.add(Sum([If(day_city[day] == list(cities.keys()).index("Bucharest"), 1, 0) 
               for day in range(4)]) == 4)
    # Seville: 5 days between day 8-12
    s.add(Sum([If(day_city[day] == list(cities.keys()).index("Seville"), 1, 0) 
               for day in range(7, 12)]) == 5)
    # Stockholm: 5 days
    s.add(Sum([If(day_city[day] == list(cities.keys()).index("Stockholm"), 1, 0) 
               for day in range(days)]) == 5)
    # Munich: 5 days between day 4-8
    s.add(Sum([If(day_city[day] == list(cities.keys()).index("Munich"), 1, 0) 
               for day in range(3, 8)]) == 5)
    # Milan: 2 days
    s.add(Sum([If(day_city[day] == list(cities.keys()).index("Milan"), 1, 0) 
               for day in range(days)]) == 2)
    
    # 4. Initial constraint: start in Bucharest
    s.add(day_city[0] == list(cities.keys()).index("Bucharest"))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        
        # Extract the itinerary
        itinerary = []
        current_city = None
        start_day = 1
        
        for day in range(1, days+1):
            city_idx = model.evaluate(day_city[day-1]).as_long()
            city = list(cities.keys())[city_idx]
            
            if day < days and model.evaluate(flight_taken[day-1]):
                # Flight day - show both cities
                next_city_idx = model.evaluate(day_city[day]).as_long()
                next_city = list(cities.keys())[next_city_idx]
                
                if current_city is not None:
                    if start_day == day:
                        itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
                
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": next_city})
                current_city = next_city
                start_day = day + 1
            else:
                if current_city is None:
                    current_city = city
                    start_day = day
                elif city != current_city:
                    if start_day == day:
                        itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_city})
                    current_city = city
                    start_day = day
        
        # Add the last segment
        if current_city is not None:
            if start_day == days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))