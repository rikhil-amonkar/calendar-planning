from z3 import *
import json

def main():
    # City indices
    cities = {
        "Venice": 0,
        "Barcelona": 1,
        "Copenhagen": 2,
        "Lyon": 3,
        "Reykjavik": 4,
        "Dubrovnik": 5,
        "Athens": 6,
        "Tallinn": 7,
        "Munich": 8
    }
    
    # Durations for each city
    durations = [4, 3, 4, 4, 4, 5, 2, 5, 3]
    
    # Direct flights (as undirected edges)
    edges = [
        (2,6), (2,5), (8,7), (2,8), (0,8), (4,6), (6,5), (0,6), (3,1),
        (2,4), (4,8), (6,8), (3,8), (1,4), (1,5), (0,2), (3,0), (5,8),
        (1,6), (2,1), (0,1), (1,8), (1,7), (2,7)
    ]
    
    # Create symmetric graph (both directions)
    graph = set()
    for (a, b) in edges:
        graph.add((a, b))
        graph.add((b, a))
    
    solver = Solver()
    
    # Order of cities (permutation of 0..8)
    order = [Int('order_%d' % i) for i in range(9)]
    for i in range(9):
        solver.add(order[i] >= 0, order[i] < 9)
    solver.add(Distinct(order))
    
    # Position array (inverse of order)
    position = [Int('pos_%d' % i) for i in range(9)]
    for i in range(9):
        solver.add(position[i] >= 0, position[i] < 9)
    solver.add(Distinct(position))
    for k in range(9):
        solver.add(position[order[k]] == k)
    
    # Cumulative durations array
    cumulative = [Int('cumulative_%d' % i) for i in range(9)]
    duration_array = Array('durations', IntSort(), IntSort())
    for i in range(9):
        solver.add(duration_array[i] == durations[i])
    
    solver.add(cumulative[0] == Select(duration_array, order[0]))
    for i in range(1, 9):
        solver.add(cumulative[i] == cumulative[i-1] + Select(duration_array, order[i]))
    
    # Direct flight constraints between consecutive cities
    for i in range(8):
        solver.add(Or(
            (order[i], order[i+1]) in graph,
            (order[i+1], order[i]) in graph  # Redundant but safe
        ))
    
    # Event constraints
    # Barcelona (index1) must have at least one day between 10 and 12
    k_barcelona = position[1]
    start_barcelona = If(k_barcelona == 0, 1, cumulative[k_barcelona-1] - (k_barcelona-1))
    end_barcelona = cumulative[k_barcelona] - k_barcelona
    solver.add(And(start_barcelona <= 12, end_barcelona >= 10))
    
    # Copenhagen (index2) must have at least one day between 7 and 10
    k_copenhagen = position[2]
    start_copenhagen = If(k_copenhagen == 0, 1, cumulative[k_copenhagen-1] - (k_copenhagen-1))
    end_copenhagen = cumulative[k_copenhagen] - k_copenhagen
    solver.add(And(start_copenhagen <= 10, end_copenhagen >= 7))
    
    # Dubrovnik (index5) must have at least one day between 16 and 20
    k_dubrovnik = position[5]
    start_dubrovnik = If(k_dubrovnik == 0, 1, cumulative[k_dubrovnik-1] - (k_dubrovnik-1))
    end_dubrovnik = cumulative[k_dubrovnik] - k_dubrovnik
    solver.add(And(start_dubrovnik <= 20, end_dubrovnik >= 16))
    
    if solver.check() == sat:
        model = solver.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(9)]
        cumulative_val = [model.evaluate(cumulative[i]).as_long() for i in range(9)]
        
        # Map index to city name
        index_to_city = {v: k for k, v in cities.items()}
        
        itinerary = []
        for idx in range(9):
            city_index = order_val[idx]
            city_name = index_to_city[city_index]
            if idx == 0:
                start_day = 1
            else:
                start_day = cumulative_val[idx-1] - (idx-1) + 1
            end_day = cumulative_val[idx] - idx
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No valid itinerary found"}')

if __name__ == "__main__":
    main()