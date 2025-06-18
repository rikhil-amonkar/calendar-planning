from z3 import *

def main():
    cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
    durations = [4, 3, 4, 5, 5, 2, 5, 4]
    
    graph = {
        0: [4, 7, 5, 1, 3, 6],   # Vienna
        1: [0, 6, 7],              # Lyon
        2: [7, 4],                 # Edinburgh
        3: [0, 4, 7],              # Reykjavik
        4: [3, 6, 0, 2, 5],        # Stuttgart
        5: [7, 6, 0, 4],           # Manchester
        6: [4, 5, 7, 1, 0],        # Split
        7: [5, 2, 0, 6, 1, 3]      # Prague
    }
    
    s = Solver()
    
    n = 8
    order = [Int(f"order_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    s.add(start[0] == 1)
    for i in range(n-1):
        s.add(start[i+1] == start[i] + durations[order[i]] - 1)
    s.add(start[n-1] + durations[order[n-1]] - 1 == 25)
    
    for j in range(n):
        s.add(If(order[j] == 2, start[j] == 5, True))
        s.add(If(order[j] == 6, start[j] == 19, True))
    
    for i in range(n-1):
        current = order[i]
        next_city = order[i+1]
        edges = graph[current]
        s.add(Or([next_city == adj for adj in edges]))
    
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(n)]
        start_val = [model.evaluate(start[i]).as_long() for i in range(n)]
        end_val = [start_val[i] + durations[order_val[i]] - 1 for i in range(n)]
        
        itinerary = []
        for i in range(n):
            city_name = cities[order_val[i]]
            s_day = start_val[i]
            e_day = end_val[i]
            if s_day == e_day:
                day_range_str = f"Day {s_day}"
            else:
                day_range_str = f"Day {s_day}-{e_day}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            if i < n-1:
                flight_day = end_val[i]
                itinerary.append({"day_range": f"Day {flight_day}", "place": city_name})
                next_city_name = cities[order_val[i+1]]
                itinerary.append({"day_range": f"Day {flight_day}", "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()