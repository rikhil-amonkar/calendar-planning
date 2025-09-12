import z3
import json

def main():
    # Define city mapping
    cities = ["Valencia", "Oslo", "Lyon", "Prague", "Paris", "Nice", "Seville", "Tallinn", "Mykonos", "Lisbon"]
    city_dict = {name: idx for idx, name in enumerate(cities)}
    
    # Direct flights set (as symmetric pairs)
    direct_flights_list = [
        (9,4), (2,5), (7,1), (3,2), (4,1), (9,6), (3,9), (1,5), (0,4), (0,9),
        (4,5), (5,8), (4,2), (0,2), (3,1), (3,4), (6,4), (1,2), (3,0), (9,5),
        (9,1), (0,6), (9,2), (4,7), (3,7)
    ]
    direct_flights_set = set()
    for a, b in direct_flights_list:
        direct_flights_set.add((min(a, b), max(a, b)))
    
    # Initialize solver
    solver = z3.Solver()
    
    # Decision variables: x[i] for day i (0-indexed for day1 to day25)
    x = [z3.Int(f'x_{i}') for i in range(25)]
    
    # Each day's city must be between 0 and 9
    for i in range(25):
        solver.add(z3.And(x[i] >= 0, x[i] <= 9))
    
    # Flight constraints: if city changes, must have direct flight
    for i in range(1, 25):
        prev_city = x[i-1]
        curr_city = x[i]
        # If cities are different, check direct flight exists
        solver.add(
            z3.Implies(
                prev_city != curr_city,
                z3.Or([z3.And(prev_city == a, curr_city == b) for (a, b) in direct_flights_set]) 
            )
        )
    
    # Function to compute if in city c on day i
    def in_city(day, city):
        # Day is 1-indexed, convert to 0-indexed
        idx = day - 1
        if day == 1:
            return x[0] == city
        else:
            return z3.Or(x[idx] == city, x[idx-1] == city)
    
    # Total days constraints per city
    total_days = [0] * 10
    for c in range(10):
        # Day 1
        total = z3.If(x[0] == c, 1, 0)
        # Days 2 to 25
        for i in range(1, 25):
            total += z3.If(z3.Or(x[i] == c, x[i-1] == c), 1, 0)
        solver.add(total == [2, 3, 4, 3, 4, 4, 5, 2, 5, 2][c])
    
    # Specific constraints
    # Valencia on day 3 and 4
    solver.add(in_city(3, city_dict["Valencia"]))
    solver.add(in_city(4, city_dict["Valencia"]))
    
    # Oslo between day 13 and 15 (at least one day)
    solver.add(z3.Or(
        in_city(13, city_dict["Oslo"]),
        in_city(14, city_dict["Oslo"]),
        in_city(15, city_dict["Oslo"])
    ))
    
    # Seville from day 5 to 9
    for day in range(5, 10):
        solver.add(in_city(day, city_dict["Seville"]))
    
    # Mykonos from day 21 to 25
    for day in range(21, 26):
        solver.add(in_city(day, city_dict["Mykonos"]))
    
    # Check feasibility
    if solver.check() == z3.sat:
        model = solver.model()
        x_vals = [model.evaluate(x[i]).as_long() for i in range(25)]
        
        # Group consecutive days with same city
        itinerary = []
        start_day = 1
        current_city = x_vals[0]
        for day in range(1, 25):
            if x_vals[day] != current_city:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": cities[current_city]
                })
                start_day = day + 1
                current_city = x_vals[day]
        itinerary.append({
            "day_range": f"Day {start_day}-25",
            "place": cities[current_city]
        })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()