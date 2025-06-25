from z3 import *
import json

def main():
    cities = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
    req_list = [2, 2, 3, 2, 5, 5, 5, 5, 4]
    oslo_id = 0
    tallinn_id = 4
    
    graph_dict = {
        'Oslo': ['Porto', 'Edinburgh', 'Budapest', 'Geneva', 'Helsinki', 'Vilnius', 'Riga', 'Tallinn'],
        'Helsinki': ['Vilnius', 'Riga', 'Edinburgh', 'Budapest', 'Oslo', 'Geneva', 'Tallinn'],
        'Edinburgh': ['Budapest', 'Geneva', 'Porto', 'Oslo', 'Helsinki', 'Riga'],
        'Riga': ['Tallinn', 'Vilnius', 'Oslo', 'Helsinki', 'Edinburgh'],
        'Tallinn': ['Vilnius', 'Helsinki', 'Oslo'],
        'Budapest': ['Edinburgh', 'Geneva', 'Helsinki', 'Oslo'],
        'Vilnius': ['Helsinki', 'Oslo'],
        'Porto': ['Oslo', 'Edinburgh', 'Geneva'],
        'Geneva': ['Edinburgh', 'Budapest', 'Oslo', 'Helsinki', 'Porto']
    }
    
    adj = [[False]*9 for _ in range(9)]
    for i, city1 in enumerate(cities):
        neighbors = graph_dict[city1]
        for neighbor in neighbors:
            j = cities.index(neighbor)
            adj[i][j] = True
            
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(9)]
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    start = [Int(f'start_{i}') for i in range(9)]
    s.add(start[0] == 1)
    
    for i in range(1, 9):
        term = req_list[8]
        for j in range(7, -1, -1):
            term = If(order[i-1] == j, req_list[j], term)
        s.add(start[i] == start[i-1] + term - 1)
    
    oslo_constraint = Or([And(order[i] == oslo_id, Or(start[i] == 23, start[i] == 24)) for i in range(9)])
    s.add(oslo_constraint)
    
    tallinn_constraint = Or([And(order[i] == tallinn_id, start[i] <= 8) for i in range(9)])
    s.add(tallinn_constraint)
    
    for i in range(8):
        conds = []
        for x in range(9):
            for y in range(9):
                if adj[x][y]:
                    conds.append(And(order[i] == x, order[i+1] == y))
        s.add(Or(conds))
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(9)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(9)]
        
        itinerary = []
        for i in range(9):
            city_index = order_val[i]
            city_name = cities[city_index]
            s_i = start_val[i]
            duration = req_list[city_index]
            e_i = s_i + duration - 1
            itinerary.append({"day_range": f"Day {s_i}-{e_i}", "place": city_name})
            if i < 8:
                next_city_index = order_val[i+1]
                next_city_name = cities[next_city_index]
                itinerary.append({"day_range": f"Day {e_i}", "place": city_name})
                itinerary.append({"day_range": f"Day {e_i}", "place": next_city_name})
                
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()