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
    
    # Fixed intervals
    fixed_intervals = {
        "Prague": (1, 3),
        "Warsaw": (20, 23),
        "Porto": (16, 20),
        "London": (3, 5),
        "Lisbon": (5, 9)
    }
    
    # Direct flights
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
    
    # Create Z3 variables for start and end days of each city
    starts = {city: Int(f'start_{city}') for city in cities}
    ends = {city: Int(f'end_{city}') for city in cities}
    
    s = Solver()
    
    # Add constraints for each city
    for city in cities:
        duration = cities[city]
        s.add(ends[city] - starts[city] + 1 == duration)
        s.add(starts[city] >= 1)
        s.add(ends[city] <= 26)
    
    # Add fixed intervals constraints
    for city, (fixed_start, fixed_end) in fixed_intervals.items():
        s.add(starts[city] <= fixed_start)
        s.add(ends[city] >= fixed_end)
    
    # Model the sequence of visits
    num_cities = len(cities)
    city_list = list(cities.keys())
    
    # We need to model the order in which cities are visited.
    # Let's use an array where position i represents the ith city visited.
    visit_order = [Int(f'visit_{i}') for i in range(num_cities)]
    
    # Each visit_order[i] is an index (0..num_cities-1) representing the city.
    for i in range(num_cities):
        s.add(visit_order[i] >= 0)
        s.add(visit_order[i] < num_cities)
    
    # All visits are distinct
    s.add(Distinct(visit_order))
    
    # The first city starts on day 1
    first_city = city_list[0]
    s.add(starts[first_city] == 1)
    
    # The last city ends on day 26
    last_city = city_list[-1]
    s.add(ends[last_city] == 26)
    
    # Consecutive cities must have starts[next] == ends[current]
    for i in range(num_cities - 1):
        current_city = city_list[i]
        next_city = city_list[i + 1]
        s.add(starts[next_city] == ends[current_city])
        # Ensure there's a direct flight from current to next
        s.add(Or(*[next_city == fc for fc in direct_flights[current_city]]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the order of cities
        order = []
        for i in range(num_cities):
            val = model[visit_order[i]].as_long()
            order.append(city_list[val])
        
        # Build the itinerary
        itinerary = []
        for city in order:
            start = model[starts[city]].as_long()
            end = model[ends[city]].as_long()
            for day in range(start, end + 1):
                itinerary.append({"day": day, "place": city})
        
        # Sort itinerary by day
        itinerary.sort(key=lambda x: x["day"])
        
        # Prepare the output
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver and print the result
result = solve_itinerary()
print(result)