from z3 import *
import json

def main():
    cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
    city_days = [2, 3, 4, 3, 4, 4, 5, 2, 5, 2]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    flight_strings = [
        "Lisbon and Paris", "Lyon and Nice", "Tallinn and Oslo", "Prague and Lyon",
        "Paris and Oslo", "Lisbon and Seville", "Prague and Lisbon", "Oslo and Nice",
        "Valencia and Paris", "Valencia and Lisbon", "Paris and Nice", "Nice and Mykonos",
        "Paris and Lyon", "Valencia and Lyon", "Prague and Oslo", "Prague and Paris",
        "Seville and Paris", "Oslo and Lyon", "Prague and Valencia", "Lisbon and Nice",
        "Lisbon and Oslo", "Valencia and Seville", "Lisbon and Lyon", "Paris and Tallinn",
        "Prague and Tallinn"
    ]
    
    allowed_edges = set()
    for flight in flight_strings:
        parts = flight.split(" and ")
        idx1 = city_to_index[parts[0]]
        idx2 = city_to_index[parts[1]]
        edge = (min(idx1, idx2), max(idx1, idx2))
        allowed_edges.add(edge)
    
    directed_edges = set()
    for (u, v) in allowed_edges:
        directed_edges.add((u, v))
        directed_edges.add((v, u))
    
    s = Solver()
    
    order = [Int(f"order_{i}") for i in range(10)]
    s_pos = [Int(f"s_pos_{i}") for i in range(10)]
    start_day = [Int(f"start_day_{j}") for j in range(10)]
    
    days_arr = Array('days_arr', IntSort(), IntSort())
    for j in range(10):
        s.add(days_arr[j] == city_days[j])
    
    s.add(Distinct(order))
    for i in range(10):
        s.add(And(order[i] >= 0, order[i] < 10))
    
    s.add(s_pos[0] == 1)
    
    for i in range(1, 10):
        prev_city = order[i-1]
        s.add(s_pos[i] == s_pos[i-1] + Select(days_arr, prev_city) - 1)
    
    for j in range(10):
        s.add(Or([And(order[i] == j, start_day[j] == s_pos[i]) for i in range(10)]))
    
    valencia_index = cities.index('Valencia')
    oslo_index = cities.index('Oslo')
    seville_index = cities.index('Seville')
    mykonos_index = cities.index('Mykonos')
    
    s.add(And(start_day[valencia_index] >= 2, start_day[valencia_index] <= 4))
    s.add(And(start_day[oslo_index] >= 11, start_day[oslo_index] <= 15))
    s.add(start_day[seville_index] <= 9)
    s.add(And(start_day[mykonos_index] >= 17, start_day[mykonos_index] <= 21))
    
    for i in range(9):
        a = order[i]
        b = order[i+1]
        edge_constraints = []
        for (u, v) in directed_edges:
            edge_constraints.append(And(a == u, b == v))
        s.add(Or(edge_constraints))
    
    last_city = order[9]
    total_days = s_pos[9] + Select(days_arr, last_city) - 1
    s.add(total_days == 25)
    
    if s.check() == sat:
        model = s.model()
        start_day_vals = [model.evaluate(start_day[j]).as_long() for j in range(10)]
        
        itinerary = []
        for j in range(10):
            city_name = cities[j]
            start = start_day_vals[j]
            end = start + city_days[j] - 1
            for day in range(start, end + 1):
                itinerary.append({"day": day, "city": city_name})
        
        itinerary_sorted = sorted(itinerary, key=lambda x: x['day'])
        result = {'itinerary': itinerary_sorted}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()