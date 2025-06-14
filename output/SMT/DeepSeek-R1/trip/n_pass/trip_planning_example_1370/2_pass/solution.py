from z3 import *

def main():
    cities = ['Santorini', 'Krakow', 'Paris', 'Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
    days_required = [5, 5, 5, 3, 5, 2, 4, 5, 4]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    graph = set()
    
    bidirectional = [
        ("Paris", "Krakow"),
        ("Paris", "Amsterdam"),
        ("Paris", "Split"),
        ("Paris", "Geneva"),
        ("Amsterdam", "Geneva"),
        ("Munich", "Split"),
        ("Split", "Krakow"),
        ("Munich", "Amsterdam"),
        ("Budapest", "Amsterdam"),
        ("Split", "Geneva"),
        ("Vilnius", "Split"),
        ("Munich", "Geneva"),
        ("Munich", "Krakow"),
        ("Vilnius", "Amsterdam"),
        ("Budapest", "Paris"),
        ("Krakow", "Amsterdam"),
        ("Vilnius", "Paris"),
        ("Budapest", "Geneva"),
        ("Split", "Amsterdam"),
        ("Santorini", "Geneva"),
        ("Amsterdam", "Santorini"),
        ("Munich", "Budapest"),
        ("Munich", "Paris")
    ]
    for a, b in bidirectional:
        u = city_to_index[a]
        v = city_to_index[b]
        graph.add((u, v))
        graph.add((v, u))
    
    unidirectional = [
        ("Vilnius", "Munich"),
        ("Krakow", "Vilnius")
    ]
    for a, b in unidirectional:
        u = city_to_index[a]
        v = city_to_index[b]
        graph.add((u, v))
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(9)]
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    arrival = [Int(f'arrival_{i}') for i in range(9)]
    departure = [Int(f'departure_{i}') for i in range(9)]
    
    for i in range(9):
        s.add(departure[i] == arrival[i] + days_required[i] - 1)
        s.add(arrival[i] >= 1, arrival[i] <= 30)
        s.add(departure[i] >= 1, departure[i] <= 30)
    
    s.add(arrival[city_to_index['Santorini']] <= 29, departure[city_to_index['Santorini']] >= 25)
    s.add(arrival[city_to_index['Krakow']] <= 22, departure[city_to_index['Krakow']] >= 18)
    s.add(arrival[city_to_index['Paris']] <= 15, departure[city_to_index['Paris']] >= 11)
    
    first_city_constraint = Or([And(order[0] == i, arrival[i] == 1) for i in range(9)])
    s.add(first_city_constraint)
    
    last_city_constraint = Or([And(order[8] == i, departure[i] == 30) for i in range(9)])
    s.add(last_city_constraint)
    
    for i in range(8):
        edge_constraints = []
        for (u, v) in graph:
            edge_constraints.append(And(order[i] == u, order[i+1] == v, arrival[v] == departure[u]))
        s.add(Or(edge_constraints))
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(9)]
        arrival_val = [m.evaluate(arrival[i]).as_long() for i in range(9)]
        departure_val = [m.evaluate(departure[i]).as_long() for i in range(9)]
        
        print("Trip Plan:")
        for pos in range(9):
            city_idx = order_val[pos]
            city_name = cities[city_idx]
            start = arrival_val[city_idx]
            end = departure_val[city_idx]
            print(f"Position {pos+1}: {city_name} from day {start} to day {end}")
        
        print("\nTravel between cities:")
        for pos in range(8):
            from_city_idx = order_val[pos]
            to_city_idx = order_val[pos+1]
            from_city = cities[from_city_idx]
            to_city = cities[to_city_idx]
            travel_day = departure_val[from_city_idx]
            print(f"Day {travel_day}: Travel from {from_city} to {to_city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()