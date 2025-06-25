from z3 import *

def main():
    # Define city mapping
    cities = [0, 1, 2, 3, 4, 5]
    city_names = {
        0: "Warsaw",
        1: "Venice",
        2: "Vilnius",
        3: "Amsterdam",
        4: "Florence",
        5: "Tallinn"
    }
    duration_map = {0: 4, 1: 3, 2: 3, 3: 2, 4: 5, 5: 2}
    
    # Define direct flight edges (symmetric)
    allowed_edges = [
        (0,1), (1,0),
        (0,2), (2,0),
        (0,3), (3,0),
        (0,5), (5,0),
        (1,3), (3,1),
        (2,3), (3,2),
        (2,5), (5,2),
        (3,4), (4,3),
        (3,5), (5,3)
    ]
    
    # Z3 variables
    city_vars = [Int(f'city_{i}') for i in range(6)]
    start_vars = [Int(f'start_{i}') for i in range(6)]
    
    s = Solver()
    
    # Each city_var is in [0,5] and all distinct
    for i in range(6):
        s.add(Or([city_vars[i] == c for c in cities]))
    s.add(Distinct(city_vars))
    
    # Start of first middle city is day 6
    s.add(start_vars[0] == 6)
    
    # Start of subsequent cities
    for i in range(1, 6):
        prev_duration = duration_map[city_vars[i-1]]
        s.add(start_vars[i] == start_vars[i-1] + prev_duration - 1)
    
    # Last city ends on day 19
    s.add(start_vars[5] + duration_map[city_vars[5]] - 1 == 19)
    
    # Tallinn must start between day 10 and 12
    for i in range(6):
        s.add(Implies(city_vars[i] == 5, And(start_vars[i] >= 10, start_vars[i] <= 12)))
    
    # Flight connections: Barcelona to first city (must be connected to Barcelona)
    s.add(Or(city_vars[0] == 0, city_vars[0] == 1, city_vars[0] == 3, city_vars[0] == 4, city_vars[0] == 5))
    
    # Last city to Hamburg (must be connected to Hamburg)
    s.add(Or(city_vars[5] == 0, city_vars[5] == 1, city_vars[5] == 3))
    
    # Adjacent cities in the middle must have direct flights
    for i in range(5):
        edge_exists = Or([And(city_vars[i] == a, city_vars[i+1] == b) for (a, b) in allowed_edges])
        s.add(edge_exists)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        city_assign = [m.evaluate(city_vars[i]).as_long() for i in range(6)]
        start_assign = [m.evaluate(start_vars[i]).as_long() for i in range(6)]
        end_assign = [start_assign[i] + duration_map[city_assign[i]] - 1 for i in range(6)]
        
        itinerary = []
        
        # Paris: days 1-2
        itinerary.append({"day_range": "Day 1-2", "place": "Paris"})
        itinerary.append({"day_range": "Day 2", "place": "Paris"})
        itinerary.append({"day_range": "Day 2", "place": "Barcelona"})
        itinerary.append({"day_range": "Day 2-6", "place": "Barcelona"})
        
        # Flight from Barcelona to first middle city on day 6
        first_city_name = city_names[city_assign[0]]
        itinerary.append({"day_range": "Day 6", "place": "Barcelona"})
        itinerary.append({"day_range": "Day 6", "place": first_city_name})
        itinerary.append({"day_range": f"Day 6-{end_assign[0]}", "place": first_city_name})
        
        # Middle cities
        for i in range(5):
            current_city_name = city_names[city_assign[i]]
            next_city_name = city_names[city_assign[i+1]]
            # Flight day: end day of current city
            flight_day = end_assign[i]
            itinerary.append({"day_range": f"Day {flight_day}", "place": current_city_name})
            itinerary.append({"day_range": f"Day {flight_day}", "place": next_city_name})
            # Next city's stay
            if i < 4:
                itinerary.append({"day_range": f"Day {flight_day}-{end_assign[i+1]}", "place": next_city_name})
            else:
                itinerary.append({"day_range": f"Day {flight_day}-19", "place": next_city_name})
        
        # Flight to Hamburg on day 19
        last_middle_city_name = city_names[city_assign[5]]
        itinerary.append({"day_range": "Day 19", "place": last_middle_city_name})
        itinerary.append({"day_range": "Day 19", "place": "Hamburg"})
        itinerary.append({"day_range": "Day 19-22", "place": "Hamburg"})
        
        # Flight to Salzburg on day 22
        itinerary.append({"day_range": "Day 22", "place": "Hamburg"})
        itinerary.append({"day_range": "Day 22", "place": "Salzburg"})
        itinerary.append({"day_range": "Day 22-25", "place": "Salzburg"})
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()