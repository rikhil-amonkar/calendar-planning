from z3 import *
import json

def main():
    # Define city names and their indices
    city_names = ["Naples", "Valencia", "Stuttgart", "Split", "Venice", "Amsterdam", "Nice", "Barcelona", "Porto"]
    city_index = {name: idx for idx, name in enumerate(city_names)}
    n_cities = len(city_names)
    
    # Durations for each city (in the order of city_index)
    durations = [3, 5, 2, 5, 5, 4, 2, 2, 4]  # Naples, Valencia, Stuttgart, Split, Venice, Amsterdam, Nice, Barcelona, Porto
    
    # Parse the flight connections
    flights_str = "Venice and Nice, Naples and Amsterdam, Barcelona and Nice, Amsterdam and Nice, Stuttgart and Valencia, Stuttgart and Porto, Split and Stuttgart, Split and Naples, Valencia and Amsterdam, Barcelona and Porto, Valencia and Naples, Venice and Amsterdam, Barcelona and Naples, Barcelona and Valencia, Split and Amsterdam, Barcelona and Venice, Stuttgart and Amsterdam, Naples and Nice, Venice and Stuttgart, Split and Barcelona, Porto and Nice, Barcelona and Stuttgart, Venice and Naples, Porto and Amsterdam, Porto and Valencia, Stuttgart and Naples, Barcelona and Amsterdam"
    flights_list = [s.strip() for s in flights_str.split(',')]
    
    # Initialize the allowed flight matrix
    allowed_matrix = [[False] * n_cities for _ in range(n_cities)]
    for flight in flights_list:
        parts = flight.split(' and ')
        if len(parts) != 2:
            continue
        c1 = parts[0].strip()
        c2 = parts[1].strip()
        i1 = city_index.get(c1)
        i2 = city_index.get(c2)
        if i1 is not None and i2 is not None:
            allowed_matrix[i1][i2] = True
            allowed_matrix[i2][i1] = True
    
    # Z3 variables: order[i] is the city index at position i
    order = [Int(f'order_{i}') for i in range(n_cities)]
    
    # Initialize solver
    solver = Solver()
    
    # Constraints: order values are between 0 and n_cities-1 and distinct
    solver.add([And(order[i] >= 0, order[i] < n_cities) for i in range(n_cities)])
    solver.add(Distinct(order))
    
    # Define allowed flight function
    allowed = Function('allowed', IntSort(), IntSort(), BoolSort())
    for i in range(n_cities):
        for j in range(n_cities):
            solver.add(allowed(i, j) == allowed_matrix[i][j])
    
    # Flight constraints between consecutive cities
    for i in range(n_cities - 1):
        solver.add(allowed(order[i], order[i+1]))
    
    # Define position of each city (0-based index in the order)
    pos = []
    for c in range(n_cities):
        expr = Sum([j * If(order[j] == c, 1, 0) for j in range(n_cities)])
        pos.append(expr)
    
    # Start day for each city
    s = []
    for c in range(n_cities):
        expr_list = []
        for d in range(n_cities):
            if d == c:
                continue
            expr_list.append(If(pos[d] < pos[c], durations[d], 0))
        total_duration_before = Sum(expr_list)
        s_c = 1 + total_duration_before - pos[c]
        s.append(s_c)
    
    # Add constraints for specific cities
    # Venice (index 4) must start between days 2 and 10
    solver.add(And(s[4] >= 2, s[4] <= 10))
    # Barcelona (index 7) must start between days 4 and 6
    solver.add(And(s[7] >= 4, s[7] <= 6))
    # Nice (index 6) must start on day 22 or 23
    solver.add(And(s[6] >= 22, s[6] <= 23))
    # Naples (index 0) must start between days 16 and 20
    solver.add(And(s[0] >= 16, s[0] <= 20))
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(n_cities)]
        
        # Map each city to its position in the order
        pos_list = [0] * n_cities
        for idx, city_idx in enumerate(order_val):
            pos_list[city_idx] = idx
        
        # Calculate start days for each city
        s_list = [0] * n_cities
        for c in range(n_cities):
            total_before = 0
            for d in range(n_cities):
                if d == c:
                    continue
                if pos_list[d] < pos_list[c]:
                    total_before += durations[d]
            s_list[c] = 1 + total_before - pos_list[c]
        
        # Build itinerary
        itinerary = []
        for c in range(n_cities):
            start = s_list[c]
            end = start + durations[c] - 1
            for day in range(start, end + 1):
                itinerary.append((day, city_names[c]))
        
        # Sort itinerary by day and then by city name
        itinerary_sorted = sorted(itinerary, key=lambda x: (x[0], x[1]))
        
        # Format result as JSON
        result = {
            "itinerary": [
                {"day": day, "place": city} for day, city in itinerary_sorted
            ]
        }
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()