from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Prague": 3,
        "Warsaw": 4,
        "Dublin": 3,
        "Athens": 3,
        "Vilnius": 4,
        "Porto": 5,
        "London": 3,
        "Seville": 2,
        "Lisbon": 5,
        "Dubrovnik": 3
    }
    
    # Fixed intervals (city: (start_day, end_day))
    fixed_intervals = {
        "Prague": (1, 3),
        "Warsaw": (20, 23),
        "Porto": (16, 20),
        "London": (3, 5),
        "Lisbon": (5, 9)
    }
    
    # Direct flights between cities
    direct_flights = {
        "Warsaw": ["Vilnius", "London", "Athens", "Lisbon", "Porto", "Prague", "Dublin"],
        "Vilnius": ["Warsaw", "Athens"],
        "Prague": ["Athens", "Lisbon", "London", "Warsaw", "Dublin"],
        "Athens": ["Prague", "Vilnius", "Dublin", "Warsaw", "Dubrovnik", "London", "Lisbon"],
        "London": ["Lisbon", "Dublin", "Athens", "Warsaw", "Prague"],
        "Lisbon": ["London", "Porto", "Prague", "Athens", "Warsaw", "Dublin", "Seville"],
        "Porto": ["Lisbon", "Warsaw", "Seville", "Dublin"],
        "Dublin": ["London", "Athens", "Seville", "Porto", "Prague", "Lisbon", "Dubrovnik"],
        "Seville": ["Dublin", "Porto", "Lisbon"],
        "Dubrovnik": ["Athens", "Dublin"]
    }
    
    # Create Z3 variables for start and end days
    starts = {city: Int(f'start_{city}') for city in cities}
    ends = {city: Int(f'end_{city}') for city in cities}
    
    s = Solver()
    
    # Duration constraints
    for city in cities:
        s.add(ends[city] - starts[city] + 1 == cities[city])
        s.add(starts[city] >= 1)
        s.add(ends[city] <= 26)
    
    # Fixed intervals constraints
    for city, (fixed_start, fixed_end) in fixed_intervals.items():
        s.add(starts[city] <= fixed_start)
        s.add(ends[city] >= fixed_end)
    
    # Model the sequence of visits
    num_cities = len(cities)
    city_list = list(cities.keys())
    
    # Visit order variables
    visit_order = [Int(f'visit_{i}') for i in range(num_cities)]
    
    # Each visit_order[i] represents a city index
    for i in range(num_cities):
        s.add(visit_order[i] >= 0)
        s.add(visit_order[i] < num_cities)
    
    # All visits are distinct
    s.add(Distinct(visit_order))
    
    # First city starts on day 1
    s.add(starts[city_list[visit_order[0]]] == 1)
    
    # Last city ends on day 26
    s.add(ends[city_list[visit_order[-1]]] == 26)
    
    # Consecutive cities must connect with direct flights
    for i in range(num_cities - 1):
        current_city = city_list[visit_order[i]]
        next_city = city_list[visit_order[i + 1]]
        s.add(starts[next_city] == ends[current_city])
        s.add(Or(*[next_city == fc for fc in direct_flights[current_city]]))
    
    # Ensure all days are covered
    total_days = Sum([ends[city] - starts[city] + 1 for city in cities])
    s.add(total_days == 26)
    
    # Check if solution exists
    if s.check() == sat:
        model = s.model()
        # Get visit order
        order = []
        for i in range(num_cities):
            val = model[visit_order[i]].as_long()
            order.append(city_list[val])
        
        # Build itinerary
        itinerary = []
        for city in order:
            start = model[starts[city]].as_long()
            end = model[ends[city]].as_long()
            for day in range(start, end + 1):
                itinerary.append({"day": day, "place": city})
        
        # Sort by day
        itinerary.sort(key=lambda x: x["day"])
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
print(result)