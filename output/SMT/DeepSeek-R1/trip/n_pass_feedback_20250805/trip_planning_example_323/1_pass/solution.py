from z3 import *
import json

def main():
    cities = ["London", "Oslo", "Split", "Porto"]
    n_cities = len(cities)
    n = 17  # c0 to c16
    c = [Int('c%d' % i) for i in range(n)]
    s = Solver()
    
    # Each city variable must be 0, 1, 2, or 3
    for i in range(n):
        s.add(c[i] >= 0, c[i] < n_cities)
    
    # Start in London (c0 = London)
    s.add(c[0] == 0)
    
    # Allowed flight pairs: (from, to)
    allowed_pairs = [
        (0, 1), (1, 0),
        (1, 2), (2, 1),
        (1, 3), (3, 1),
        (0, 2), (2, 0)
    ]
    
    # Flight constraints: for each day i (1 to 16), either stay in the same city or fly directly
    for i in range(1, n):
        stay = [c[i] == c[i-1]]
        flights = [And(c[i-1] == a, c[i] == b) for (a, b) in allowed_pairs]
        s.add(Or(stay + flights))
    
    # Count days for each city: a day i (1 to 16) counts for a city if the day starts or ends there
    def count_city(city_idx):
        return Sum([If(Or(c[i-1] == city_idx, c[i] == city_idx), 1, 0) for i in range(1, n)])
    
    s.add(count_city(0) == 7)  # London
    s.add(count_city(1) == 2)  # Oslo
    s.add(count_city(2) == 5)  # Split
    s.add(count_city(3) == 5)  # Porto
    
    # Must be in Split on days 7 to 11 (inclusive)
    for k in range(7, 12):
        s.add(Or(c[k-1] == 2, c[k] == 2))
    
    # Cannot be in Split on days 1-6 and 12-16
    for i in range(1, 7):
        s.add(And(c[i-1] != 2, c[i] != 2))
    for i in range(12, 17):
        s.add(And(c[i-1] != 2, c[i] != 2))
    
    # Must be in London at least once between days 1 and 7 (inclusive)
    s.add(Or([Or(c[k-1] == 0, c[k] == 0) for k in range(1, 8)]))
    
    if s.check() == sat:
        m = s.model()
        c_val = [m.evaluate(c[i]).as_long() for i in range(n)]
        itinerary = []
        for day in range(1, 17):
            city_name = cities[c_val[day]]
            itinerary.append({"day": day, "place": city_name})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()