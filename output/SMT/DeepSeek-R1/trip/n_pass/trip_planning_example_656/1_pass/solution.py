from z3 import *

def main():
    cities = ['Reykjavik', 'Istanbul', 'Edinburgh', 'Oslo', 'Stuttgart', 'Bucharest']
    days_required = [5, 4, 5, 2, 3, 5]
    n = len(cities)
    
    # Build city index map
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Define flight connections (undirected graph)
    graph = {
        'Reykjavik': ['Stuttgart', 'Oslo'],
        'Istanbul': ['Oslo', 'Bucharest', 'Edinburgh', 'Stuttgart'],
        'Edinburgh': ['Stuttgart', 'Istanbul', 'Oslo'],
        'Oslo': ['Bucharest', 'Istanbul', 'Reykjavik', 'Edinburgh'],
        'Stuttgart': ['Reykjavik', 'Edinburgh', 'Istanbul'],
        'Bucharest': ['Oslo', 'Istanbul']
    }
    
    # Build adjacency matrix
    conn_matrix = [[0]*n for _ in range(n)]
    for city, neighbors in graph.items():
        i = city_index[city]
        for neighbor in neighbors:
            j = city_index[neighbor]
            conn_matrix[i][j] = 1
            conn_matrix[j][i] = 1
    
    # Initialize Z3 variables
    solver = Solver()
    order = [Int(f'o{i}') for i in range(n)]
    offsets = [Int(f'offs{i}') for i in range(n)]
    
    # Constraints: order is a permutation of [0, n-1]
    solver.add(Distinct(order))
    for i in range(n):
        solver.add(And(order[i] >= 0, order[i] < n))
    
    # Define offsets: cumulative sum of (days - 1) for previous cities
    solver.add(offsets[0] == 0)
    for i in range(1, n):
        prev_city_days = days_required[order[i-1]]
        solver.add(offsets[i] == offsets[i-1] + (prev_city_days - 1))
    
    # Flight connection constraints
    for i in range(n-1):
        city1 = order[i]
        city2 = order[i+1]
        solver.add(conn_matrix[city1][city2] == 1)
    
    # Constraints for Istanbul and Oslo
    istanbul_idx = city_index['Istanbul']
    oslo_idx = city_index['Oslo']
    
    # Start day for a city at position k: 1 + offsets[k]
    istanbul_start = Int('istanbul_start')
    oslo_start = Int('oslo_start')
    
    # Sum over k: if order[k] is Istanbul, then start = 1 + offsets[k]
    istanbul_start_expr = 1 + Sum([If(order[k] == istanbul_idx, offsets[k], 0) for k in range(n)])
    oslo_start_expr = 1 + Sum([If(order[k] == oslo_idx, offsets[k], 0) for k in range(n)])
    solver.add(istanbul_start == istanbul_start_expr)
    solver.add(oslo_start == oslo_start_expr)
    solver.add(istanbul_start >= 2, istanbul_start <= 8)
    solver.add(oslo_start >= 7, oslo_start <= 9)
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        order_sol = [model.evaluate(order[i]).as_long() for i in range(n)]
        offsets_sol = [model.evaluate(offsets[i]).as_long() for i in range(n)]
        
        # Build itinerary
        itinerary = []
        for pos in range(n):
            city_idx = order_sol[pos]
            start_day = 1 + offsets_sol[pos]
            stay_days = days_required[city_idx]
            end_day = start_day + stay_days - 1
            city_name = cities[city_idx]
            
            # If not the first city, add arrival record
            if pos > 0:
                itinerary.append({'day_range': f'Day {start_day}', 'place': city_name})
            
            # Entire stay record
            itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': city_name})
            
            # If not the last city, add departure record
            if pos < n - 1:
                itinerary.append({'day_range': f'Day {end_day}', 'place': city_name})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()