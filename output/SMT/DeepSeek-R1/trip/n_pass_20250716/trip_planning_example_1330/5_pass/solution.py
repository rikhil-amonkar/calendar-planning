from z3 import *

def main():
    cities = ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich', 'Naples']
    days_arr = [2, 5, 4, 2, 4, 4, 3, 5, 4]
    mapping = {city: idx for idx, city in enumerate(cities)}
    
    connection_list = [
        "Zurich and Brussels", "Bucharest and Copenhagen", "Venice and Brussels",
        "Nice and Zurich", "Hamburg and Nice", "Zurich and Naples",
        "Hamburg and Bucharest", "Zurich and Copenhagen", "Bucharest and Brussels",
        "Hamburg and Brussels", "Venice and Naples", "Venice and Copenhagen",
        "Bucharest and Naples", "Hamburg and Copenhagen", "Venice and Zurich",
        "Nice and Brussels", "Hamburg and Venice", "Copenhagen and Naples",
        "Nice and Naples", "Hamburg and Zurich", "Salzburg and Hamburg",
        "Zurich and Bucharest", "Brussels and Naples", "Copenhagen and Brussels",
        "Venice and Nice", "Nice and Copenhagen"
    ]
    allowed_edges = set()
    for conn in connection_list:
        parts = conn.split(' and ')
        city1, city2 = parts[0].strip(), parts[1].strip()
        idx1, idx2 = mapping[city1], mapping[city2]
        allowed_edges.add((idx1, idx2))
        allowed_edges.add((idx2, idx1))
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(9)]
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    arrival_pos = [Int(f'arrival_pos_{i}') for i in range(9)]
    s.add(arrival_pos[0] == 1)
    
    durations_arr = Array('durations', IntSort(), IntSort())
    for i in range(9):
        s.add(durations_arr[i] == days_arr[i])
    
    for i in range(1, 9):
        prev_duration = durations_arr[order[i-1]]
        s.add(arrival_pos[i] == arrival_pos[i-1] + prev_duration - 1)
    
    for i in range(8):
        constraints = []
        for edge in allowed_edges:
            a, b = edge
            constraints.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(constraints))
    
    s.add(arrival_pos[8] + durations_arr[order[8]] - 1 == 25)
    
    brussels_idx = 3
    copenhagen_idx = 5
    nice_idx = 6
    naples_idx = 8
    
    brussels_arrival = Int('brussels_arrival')
    brussels_arrival_expr = Sum([If(order[i] == brussels_idx, arrival_pos[i], 0) for i in range(9)])
    s.add(brussels_arrival == brussels_arrival_expr)
    s.add(brussels_arrival == 21)
    
    copenhagen_arrival = Int('copenhagen_arrival')
    copenhagen_arrival_expr = Sum([If(order[i] == copenhagen_idx, arrival_pos[i], 0) for i in range(9)])
    s.add(copenhagen_arrival == copenhagen_arrival_expr)
    s.add(Or(
        And(copenhagen_arrival >= 12, copenhagen_arrival <= 15),
        And(copenhagen_arrival >= 18, copenhagen_arrival <= 21)
    ))
    
    nice_arrival = Int('nice_arrival')
    nice_arrival_expr = Sum([If(order[i] == nice_idx, arrival_pos[i], 0) for i in range(9)])
    s.add(nice_arrival == nice_arrival_expr)
    s.add(Or(
        And(nice_arrival >= 5, nice_arrival <= 7),
        And(nice_arrival >= 9, nice_arrival <= 11)
    ))
    
    naples_arrival = Int('naples_arrival')
    naples_arrival_expr = Sum([If(order[i] == naples_idx, arrival_pos[i], 0) for i in range(9)])
    s.add(naples_arrival == naples_arrival_expr)
    s.add(Or(
        And(naples_arrival >= 16, naples_arrival <= 19),
        naples_arrival == 22
    ))
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(9)]
        arrival_vals = [m.evaluate(arrival_pos[i]).as_long() for i in range(9)]
        
        itinerary = []
        for i in range(9):
            city_idx = order_vals[i]
            city_name = cities[city_idx]
            a = arrival_vals[i]
            d = a + days_arr[city_idx] - 1
            itinerary.append({"day_range": f"Day {a}-{d}", "place": city_name})
            if i < 8:
                next_city_idx = order_vals[i+1]
                next_city_name = cities[next_city_idx]
                itinerary.append({"day_range": f"Day {d}", "place": city_name})
                itinerary.append({"day_range": f"Day {d}", "place": next_city_name})
        
        print({"itinerary": itinerary})
    else:
        print("No solution found")

if __name__ == '__main__':
    main()