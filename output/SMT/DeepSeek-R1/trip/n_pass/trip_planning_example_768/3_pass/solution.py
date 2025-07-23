from z3 import *
import json

def main():
    cities = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
    city_dict = {i: cities[i] for i in range(6)}
    
    edges_list = [
        (2, 3),  # London - Copenhagen
        (3, 5),  # Copenhagen - Tallinn
        (5, 4),  # Tallinn - Oslo
        (0, 2),  # Mykonos - London
        (4, 1),  # Oslo - Nice
        (2, 1),  # London - Nice
        (0, 1),  # Mykonos - Nice
        (2, 4),  # London - Oslo
        (3, 1),  # Copenhagen - Nice
        (3, 4)   # Copenhagen - Oslo
    ]
    edges_sym = set()
    for (a, b) in edges_list:
        edges_sym.add((a, b))
        edges_sym.add((b, a))
    
    start = Int('start')
    city = [Int('city_%d' % i) for i in range(16)]
    
    s = Solver()
    
    s.add(start >= 0, start <= 5)
    for i in range(16):
        s.add(city[i] >= 0, city[i] <= 5)
    
    def valid_flight(x, y):
        options = []
        for (a, b) in edges_sym:
            options.append(And(x == a, y == b))
        return Or(options)
    
    s.add(Or(start == city[0], valid_flight(start, city[0])))
    
    for i in range(15):
        s.add(Or(city[i] == city[i+1], valid_flight(city[i], city[i+1])))
    
    counts = [0] * 6
    for c in range(6):
        total = 0
        for d in range(1, 17):
            if d == 1:
                cond = Or(start == c, city[0] == c)
            else:
                cond = Or(city[d-2] == c, city[d-1] == c)
            total += If(cond, 1, 0)
        counts[c] = total
    
    s.add(counts[0] == 4)  # Mykonos
    s.add(counts[1] == 3)  # Nice
    s.add(counts[2] == 2)  # London
    s.add(counts[3] == 3)  # Copenhagen
    s.add(counts[4] == 5)  # Oslo
    s.add(counts[5] == 4)  # Tallinn
    
    # Nice must be visited on days 14 and 16
    s.add(Or(city[12] == 1, city[13] == 1))  # Day 14
    s.add(Or(city[14] == 1, city[15] == 1))  # Day 16
    
    # Oslo must have at least one full day between days 10-14
    oslo_cond = Or(
        And(city[8] == 4, city[9] == 4),   # Day 10
        And(city[9] == 4, city[10] == 4),  # Day 11
        And(city[10] == 4, city[11] == 4), # Day 12
        And(city[11] == 4, city[12] == 4), # Day 13
        And(city[12] == 4, city[13] == 4)  # Day 14
    )
    s.add(oslo_cond)
    
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        city_vals = [m[c].as_long() for c in city]
        
        itinerary_list = []
        # Day 1: starts at start_val, ends at city_vals[0]
        itinerary_list.append({"day": 1, "city": cities[start_val]})
        if start_val != city_vals[0]:
            itinerary_list.append({"day": 1, "city": cities[city_vals[0]]})
        
        # Days 2-16
        for day in range(2, 17):
            # Start city is previous day's end city
            start_city = city_vals[day-2]
            end_city = city_vals[day-1]
            itinerary_list.append({"day": day, "city": cities[start_city]})
            if start_city != end_city:
                itinerary_list.append({"day": day, "city": cities[end_city]})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()