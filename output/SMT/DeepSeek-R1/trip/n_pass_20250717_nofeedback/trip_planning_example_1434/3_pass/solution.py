import json
from z3 import *

def main():
    cities = [
        "Rome",          #0
        "Mykonos",       #1
        "Lisbon",        #2
        "Frankfurt",     #3
        "Nice",          #4
        "Stuttgart",     #5
        "Venice",        #6
        "Dublin",        #7
        "Bucharest",     #8
        "Seville"        #9
    ]
    durations = [3, 2, 2, 5, 3, 4, 4, 2, 2, 5]  # Corresponding to the cities list

    flight_strings = [
        "Rome and Stuttgart", "Venice and Rome", "Dublin and Bucharest",
        "Mykonos and Rome", "Seville and Lisbon", "Frankfurt and Venice",
        "Venice and Stuttgart", "Bucharest and Lisbon", "Nice and Mykonos",
        "Venice and Lisbon", "Dublin and Lisbon", "Venice and Nice",
        "Rome and Seville", "Frankfurt and Rome", "Nice and Dublin",
        "Rome and Bucharest", "Frankfurt and Dublin", "Rome and Dublin",
        "Venice and Dublin", "Rome and Lisbon", "Frankfurt and Lisbon",
        "Nice and Rome", "Frankfurt and Nice", "Frankfurt and Stuttgart",
        "Frankfurt and Bucharest", "Lisbon and Stuttgart", "Nice and Lisbon",
        "Seville and Dublin"
    ]
    
    flight_set = set()
    for s in flight_strings:
        parts = s.split(' and ')
        idx1 = cities.index(parts[0])
        idx2 = cities.index(parts[1])
        flight_set.add((min(idx1, idx2), max(idx1, idx2)))
    
    n = 10
    s = Solver()
    
    # Z3 array for city durations
    dur_array = Array('dur_array', IntSort(), IntSort())
    for idx, d in enumerate(durations):
        s.add(dur_array[idx] == d)
    
    order = [Int('order_%d' % i) for i in range(n)]
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    start = [Int('start_%d' % i) for i in range(n)]
    s.add(start[0] == 1)
    
    for i in range(1, n):
        prev_city = order[i-1]
        prev_dur = dur_array[prev_city]
        s.add(start[i] == start[i-1] + prev_dur - 1)
    
    last_city = order[n-1]
    last_dur = dur_array[last_city]
    s.add(start[n-1] + last_dur - 1 == 23)
    
    mykonos_index = cities.index("Mykonos")
    seville_index = cities.index("Seville")
    frankfurt_index = cities.index("Frankfurt")
    
    mykonos_constraint = Or([And(order[i] == mykonos_index, start[i] == 10) for i in range(n)])
    s.add(mykonos_constraint)
    
    seville_constraint = Or([And(order[i] == seville_index, start[i] == 13) for i in range(n)])
    s.add(seville_constraint)
    
    frankfurt_constraint = Or([And(order[i] == frankfurt_index, start[i] <= 5) for i in range(n)])
    s.add(frankfurt_constraint)
    
    for i in range(n-1):
        city1 = order[i]
        city2 = order[i+1]
        flight_cond = Or([Or(And(city1 == a, city2 == b), And(city1 == b, city2 == a)) for (a, b) in flight_set])
        s.add(flight_cond)
    
    if s.check() == sat:
        model = s.model()
        order_vals = [model.evaluate(order[i]).as_long() for i in range(n)]
        start_vals = [model.evaluate(start[i]).as_long() for i in range(n)]
        
        itinerary_list = []
        for i in range(n):
            city_idx = order_vals[i]
            city_name = cities[city_idx]
            dur = durations[city_idx]
            s_day = start_vals[i]
            for d in range(s_day, s_day + dur):
                itinerary_list.append({"day": d, "place": city_name})
        
        itinerary_list.sort(key=lambda x: x["day"])
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()