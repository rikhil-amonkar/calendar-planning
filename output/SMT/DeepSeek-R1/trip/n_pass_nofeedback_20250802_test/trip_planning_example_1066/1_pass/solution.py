from z3 import *

def main():
    cities = ["Brussels", "Bucharest", "Stuttgart", "Mykonos", "Madrid", "Helsinki", "Split", "London"]
    days_req = [4, 3, 4, 2, 2, 5, 3, 5]  # Corresponding to the cities list

    # Direct flights as tuples of indices
    flights = [
        (5, 7), (6, 4), (5, 4), (7, 4), (0, 7), (1, 7), (0, 1), (1, 4),
        (6, 5), (3, 4), (2, 7), (5, 0), (0, 4), (6, 7), (2, 6), (7, 3)
    ]
    direct_flights_set = set()
    for (a, b) in flights:
        direct_flights_set.add((a, b))
        direct_flights_set.add((b, a))
    
    s = Solver()
    c = [Int('c_%d' % i) for i in range(21)]
    
    # Each day's city must be between 0 and 7
    for i in range(21):
        s.add(c[i] >= 0, c[i] < 8)
    
    # Flight constraints: consecutive days must be the same or have a direct flight
    for i in range(20):
        current = c[i]
        next_city = c[i+1]
        s.add(If(current != next_city,
                 Or([And(current == a, next_city == b) for (a, b) in direct_flights_set]),
                 True))
    
    # Count the days for each city
    for city_idx in range(8):
        total = 0
        # Day 0 (first day)
        total += If(c[0] == city_idx, 1, 0)
        for d in range(1, 21):
            # Condition: either today's city is the target, or yesterday was the target and today is different
            cond = Or(c[d] == city_idx, And(c[d-1] == city_idx, c[d] != city_idx))
            total += If(cond, 1, 0)
        s.add(total == days_req[city_idx])
    
    # Madrid must be on day 20 and 21
    s.add(c[19] == 4)  # Day 20
    s.add(c[20] == 4)  # Day 21
    
    # Stuttgart must be present between day 1 and day 4 (indices 0 to 3)
    stuttgart_conds = []
    for d in range(4):  # Days 1 to 4: indices 0,1,2,3
        if d == 0:
            cond = (c[0] == 2)
        else:
            cond = Or(c[d] == 2, And(c[d-1] == 2, c[d] != 2))
        stuttgart_conds.append(cond)
    s.add(Or(stuttgart_conds))
    
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for i in range(21):
            city_index = model.eval(c[i]).as_long()
            itinerary_list.append({"day": i+1, "place": cities[city_index]})
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()