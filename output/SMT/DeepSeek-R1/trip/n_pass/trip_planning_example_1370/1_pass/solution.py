from z3 import *
import json

def main():
    cities = ['Santorini', 'Krakow', 'Paris', 'Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
    days_required = [5, 5, 5, 3, 5, 2, 4, 5, 4]
    
    edges = []
    def add_bidir(i, j):
        edges.append((i, j))
        edges.append((j, i))
    
    add_bidir(2, 1)   # Paris - Krakow
    add_bidir(2, 6)   # Paris - Amsterdam
    add_bidir(2, 8)   # Paris - Split
    edges.append((3, 4))  # Vilnius to Munich (directed)
    add_bidir(2, 5)   # Paris - Geneva
    add_bidir(6, 5)   # Amsterdam - Geneva
    add_bidir(4, 8)   # Munich - Split
    add_bidir(8, 1)   # Split - Krakow
    add_bidir(4, 6)   # Munich - Amsterdam
    add_bidir(7, 6)   # Budapest - Amsterdam
    add_bidir(8, 5)   # Split - Geneva
    add_bidir(3, 8)   # Vilnius - Split
    add_bidir(4, 5)   # Munich - Geneva
    add_bidir(4, 1)   # Munich - Krakow
    edges.append((1, 3))  # Krakow to Vilnius (directed)
    add_bidir(3, 6)   # Vilnius - Amsterdam
    add_bidir(7, 2)   # Budapest - Paris
    add_bidir(1, 6)   # Krakow - Amsterdam
    add_bidir(3, 2)   # Vilnius - Paris
    add_bidir(7, 5)   # Budapest - Geneva
    add_bidir(8, 6)   # Split - Amsterdam
    add_bidir(0, 5)   # Santorini - Geneva
    add_bidir(0, 6)   # Santorini - Amsterdam
    add_bidir(4, 7)   # Munich - Budapest
    add_bidir(4, 2)   # Munich - Paris

    s = Solver()
    order = [Int(f'order_{i}') for i in range(9)]
    
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    for i in range(8):
        constraints = []
        for (a, b) in edges:
            constraints.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(constraints))
    
    start_day = [Int(f'start_{i}') for i in range(9)]
    end_day = [Int(f'end_{i}') for i in range(9)]
    
    s.add(start_day[0] == 1)
    s.add(end_day[0] == start_day[0] + days_required[order[0]] - 1)
    
    for i in range(1, 9):
        s.add(start_day[i] == end_day[i-1])
        s.add(end_day[i] == start_day[i] + days_required[order[i]] - 1)
    
    for i in range(9):
        city = order[i]
        s.add(If(city == 0, And(start_day[i] <= 29, end_day[i] >= 25), True))
        s.add(If(city == 1, And(start_day[i] <= 22, end_day[i] >= 18), True))
        s.add(If(city == 2, And(start_day[i] <= 15, end_day[i] >= 11), True))
    
    if s.check() == sat:
        m = s.model()
        order_val = [m[order[i]].as_long() for i in range(9)]
        start_val = [m[start_day[i]].as_long() for i in range(9)]
        end_val = [m[end_day[i]].as_long() for i in range(9)]
        
        itinerary_list = []
        for i in range(9):
            a = start_val[i]
            b = end_val[i]
            city_name = cities[order_val[i]]
            if a == b:
                day_str = f"Day {a}"
            else:
                day_str = f"Day {a}-{b}"
            itinerary_list.append({"day_range": day_str, "place": city_name})
            if i < 8:
                itinerary_list.append({"day_range": f"Day {b}", "place": city_name})
                next_city_name = cities[order_val[i+1]]
                itinerary_list.append({"day_range": f"Day {b}", "place": next_city_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()