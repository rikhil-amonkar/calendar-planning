from z3 import *
import json

def solve_scheduling_problem():
    # Define cities and required days (corrected names)
    cities = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5
    }
    
    # Fixed date constraints
    fixed_constraints = [
        ("Munich", 4, 6),
        ("Santorini", 8, 10),
        ("Valencia", 14, 15)
    ]
    
    # Direct flights (corrected)
    direct_flights = {
        "Bucharest": ["Manchester", "Valencia", "Vienna", "Munich", "Santorini"],
        "Munich": ["Venice", "Porto", "Manchester", "Reykjavik", "Vienna", "Bucharest", "Tallinn", "Valencia"],
        "Santorini": ["Manchester", "Venice", "Vienna", "Bucharest"],
        "Vienna": ["Reykjavik", "Valencia", "Manchester", "Porto", "Venice", "Bucharest", "Santorini", "Munich"],
        "Venice": ["Munich", "Santorini", "Manchester", "Vienna"],
        "Manchester": ["Bucharest", "Santorini", "Vienna", "Porto", "Venice", "Munich"],
        "Porto": ["Munich", "Vienna", "Valencia", "Manchester"],
        "Valencia": ["Vienna", "Bucharest", "Porto", "Munich"],
        "Reykjavik": ["Vienna", "Munich"],
        "Tallinn": ["Munich"]
    }
    
    solver = Solver()
    
    # Create day variables
    days = 24
    day_to_city = [Int(f"day_{i}") for i in range(1, days + 1)]
    
    # City IDs
    city_ids = {city: i for i, city in enumerate(cities.keys())}
    id_to_city = {i: city for city, i in city_ids.items()}
    
    # Each day must be assigned a valid city
    for day in day_to_city:
        solver.add(Or([day == city_ids[city] for city in cities]))
    
    # Fixed date constraints
    for city, start, end in fixed_constraints:
        for day in range(start, end + 1):
            solver.add(day_to_city[day - 1] == city_ids[city])
    
    # Duration constraints (accounting for flight days)
    for city, duration in cities.items():
        solver.add(Sum([If(day_to_city[i] == city_ids[city], 1, 0) 
                       for i in range(days)]) == duration)
    
    # Flight constraints (more flexible implementation)
    for i in range(days - 1):
        current = day_to_city[i]
        next_day = day_to_city[i + 1]
        solver.add(Or(
            current == next_day,  # Stay in same city
            *[And(current == city_ids[city1], next_day == city_ids[city2])
              for city1 in direct_flights 
              for city2 in direct_flights[city1]
        ))
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        for day in range(1, days + 1):
            city_id = model.evaluate(day_to_city[day - 1]).as_long()
            city = id_to_city[city_id]
            
            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_city = city
                start_day = day
        
        if start_day == days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_city})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found - please check constraints")

solve_scheduling_problem()