import json
from z3 import *

def main():
    cities = ["Rome", "Mykonos", "Lisbon", "Frankfurt", "Nice", "Stuttgart", "Venice", "Dublin", "Bucharest", "Seville"]
    durations = [3, 2, 2, 5, 3, 4, 4, 2, 2, 5]
    n = 10

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
    
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    flight_set = set()
    for s in flight_strings:
        parts = s.split(' and ')
        c1 = city_to_index[parts[0]]
        c2 = city_to_index[parts[1]]
        key = (min(c1, c2), max(c1, c2))
        flight_set.add(key)

    s = Solver()

    city_at_position = [Int(f'city_pos_{i}') for i in range(n)]
    for i in range(n):
        s.add(And(city_at_position[i] >= 0, city_at_position[i] < n))
    s.add(Distinct(city_at_position))

    base_arr = [Int(f'base_{i}') for i in range(n)]
    s.add(base_arr[0] == 0)
    for i in range(1, n):
        term_expr = IntVal(0)
        for j in range(n):
            term_expr = If(city_at_position[i-1] == j, durations[j] - 1, term_expr)
        s.add(base_arr[i] == base_arr[i-1] + term_expr)

    seville_idx = cities.index("Seville")
    mykonos_idx = cities.index("Mykonos")
    frankfurt_idx = cities.index("Frankfurt")
    
    for i in range(n):
        s.add(If(city_at_position[i] == seville_idx, base_arr[i] == 12, True))
        s.add(If(city_at_position[i] == mykonos_idx, Or(base_arr[i] == 8, base_arr[i] == 9, base_arr[i] == 10), True))
        s.add(If(city_at_position[i] == frankfurt_idx, base_arr[i] <= 4, True))

    for i in range(n-1):
        c1 = city_at_position[i]
        c2 = city_at_position[i+1]
        cond = BoolVal(False)
        for key in flight_set:
            cond = Or(cond, 
                      Or(
                          And(c1 == key[0], c2 == key[1]),
                          And(c1 == key[1], c2 == key[0])
                      ))
        s.add(cond)

    if s.check() == sat:
        model = s.model()
        city_sequence = []
        start_days = [0] * n
        for pos in range(n):
            city_idx = model.eval(city_at_position[pos]).as_long()
            city_sequence.append(city_idx)
            base_val = model.eval(base_arr[pos]).as_long()
            start_day = base_val + 1
            start_days[city_idx] = start_day

        itinerary_list = []
        for city_idx in range(n):
            city_name = cities[city_idx]
            start = start_days[city_idx]
            end = start + durations[city_idx] - 1
            for day in range(start, end + 1):
                itinerary_list.append({"day": day, "place": city_name})
        
        itinerary_list.sort(key=lambda x: x["day"])
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()