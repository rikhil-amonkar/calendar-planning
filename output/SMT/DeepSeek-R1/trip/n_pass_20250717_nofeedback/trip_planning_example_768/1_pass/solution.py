from z3 import *
import json

def main():
    # Define city mappings
    cities = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
    city_dict = {i: cities[i] for i in range(6)}
    
    # Define direct flight edges (both directions)
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
    
    # Create Z3 variables
    start = Int('start')
    city = [Int('city_%d' % i) for i in range(16)]  # city[i] is end of day i+1
    
    s = Solver()
    
    # Constrain variables to be in [0,5]
    s.add(start >= 0, start <= 5)
    for i in range(16):
        s.add(city[i] >= 0, city[i] <= 5)
    
    # Flight constraints
    def valid_flight(x, y):
        return Or([And(x == a, y == b) for (a, b) in edges_sym])
    
    # Day 1 flight constraint
    s.add(If(start != city[0], valid_flight(start, city[0]), True)
    
    # Flight constraints for days 2 to 16
    for i in range(15):
        s.add(If(city[i] != city[i+1], valid_flight(city[i], city[i+1]), True))
    
    # Count the days for each city
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
    
    # Add constraints for total days in each city
    s.add(counts[0] == 4)  # Mykonos
    s.add(counts[1] == 3)  # Nice
    s.add(counts[2] == 2)  # London
    s.add(counts[3] == 3)  # Copenhagen
    s.add(counts[4] == 5)  # Oslo
    s.add(counts[5] == 4)  # Tallinn
    
    # Nice must be visited on day 14 and day 16
    s.add(Or(city[12] == 1, city[13] == 1))  # Day 14: set {city[12], city[13]}
    s.add(Or(city[14] == 1, city[15] == 1))  # Day 16: set {city[14], city[15]}
    
    # Oslo must be visited between day 10 and 14 (inclusive)
    oslo_cond = Or(
        Or(city[8] == 4, city[9] == 4),  # Day 10
        Or(city[9] == 4, city[10] == 4), # Day 11
        Or(city[10] == 4, city[11] == 4), # Day 12
        Or(city[11] == 4, city[12] == 4), # Day 13
        Or(city[12] == 4, city[13] == 4)  # Day 14
    )
    s.add(oslo_cond)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for i in range(16):
            c_val = m[city[i]].as_long()
            city_name = city_dict[c_val]
            itinerary_list.append({"day": i+1, "city": city_name})
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()