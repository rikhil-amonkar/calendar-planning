from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ["Dublin", "London", "Hamburg", "Helsinki", "Reykjavik", "Mykonos"]
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    flights = [
        ("Dublin", "London"),
        ("Dublin", "Hamburg"),
        ("Dublin", "Helsinki"),
        ("Dublin", "Reykjavik"),
        ("London", "Hamburg"),
        ("London", "Reykjavik"),
        ("London", "Mykonos"),
        ("Hamburg", "Helsinki"),
        ("Helsinki", "Reykjavik"),
        ("Helsinki", "London"),
    ]
    
    # Create flight connections graph
    flight_graph = {city: set() for city in cities}
    for a, b in flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    s = Solver()
    
    # Day variables (1-16)
    days = [Int(f"day_{i}") for i in range(1, 17)]
    
    # Each day must be a valid city index
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Flight constraints between consecutive days
    for i in range(15):
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or take direct flight
        s.add(Or(
            current == next_day,
            *[And(current == city_idx[a], next_day == city_idx[b]) 
              for a in cities for b in flight_graph[a]]
        ))
    
    # Duration constraints
    def count_days(city):
        return Sum([If(d == city_idx[city], 1, 0) for d in days])
    
    s.add(count_days("Dublin") == 5)
    s.add(count_days("London") == 5)
    s.add(count_days("Hamburg") == 2)
    s.add(count_days("Helsinki") == 4)
    s.add(count_days("Reykjavik") == 2)
    s.add(count_days("Mykonos") == 3)
    
    # Event constraints
    # Wedding in Reykjavik between day 9-10
    s.add(Or(days[8] == city_idx["Reykjavik"], days[9] == city_idx["Reykjavik"]))
    
    # Show in Dublin from day 2-6
    for i in range(1, 6):
        s.add(days[i] == city_idx["Dublin"])
    
    # Meet friends in Hamburg between day 1-2
    s.add(Or(days[0] == city_idx["Hamburg"], days[1] == city_idx["Hamburg"]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current = None
        start = 1
        for day in range(1, 17):
            city = cities[m.evaluate(days[day-1]).as_long()]
            if current is None:
                current = city
                start = day
            elif city != current:
                # Add previous stay
                if start == day - 1:
                    itinerary.append({"day_range": f"Day {start}", "place": current})
                else:
                    itinerary.append({"day_range": f"Day {start}-{day-1}", "place": current})
                # Add flight day
                itinerary.append({"day_range": f"Day {day}", "place": current})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current = city
                start = day
        # Add last stay
        if start == 16:
            itinerary.append({"day_range": f"Day {start}", "place": current})
        else:
            itinerary.append({"day_range": f"Day {start}-16", "place": current})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(result)