from z3 import *
import json

def main():
    cities = ["Mykonos", "Krakow", "Vilnius", "Helsinki", "Dubrovnik", "Oslo", "Madrid", "Paris"]
    n = len(cities)
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    flight_pairs = [
        ("Oslo", "Krakow"),
        ("Oslo", "Paris"),
        ("Paris", "Madrid"),
        ("Helsinki", "Vilnius"),
        ("Oslo", "Madrid"),
        ("Oslo", "Helsinki"),
        ("Helsinki", "Krakow"),
        ("Dubrovnik", "Helsinki"),
        ("Dubrovnik", "Madrid"),
        ("Oslo", "Dubrovnik"),
        ("Krakow", "Paris"),
        ("Madrid", "Mykonos"),
        ("Oslo", "Vilnius"),
        ("Krakow", "Vilnius"),
        ("Helsinki", "Paris"),
        ("Vilnius", "Paris"),
        ("Helsinki", "Madrid")
    ]
    
    allowed_pairs = set()
    for a, b in flight_pairs:
        i1 = city_map[a]
        i2 = city_map[b]
        allowed_pairs.add((i1, i2))
        allowed_pairs.add((i2, i1))
    
    s = [Int(f's_{i}') for i in range(19)]
    
    domain_constraints = [And(0 <= s_i, s_i < n) for s_i in s]
    
    flight_constraints = []
    for i in range(18):
        prev = s[i]
        curr = s[i+1]
        flight_constraints.append(
            If(prev != curr,
               Or([And(prev == a, curr == b) for (a, b) in allowed_pairs]),
               True
            )
        )
    
    def days_in_city(city_idx):
        return Sum([If(Or(s[i] == city_idx, s[i+1] == city_idx), 1, 0) for i in range(18)])
    
    mykonos_id = city_map["Mykonos"]
    krakow_id = city_map["Krakow"]
    vilnius_id = city_map["Vilnius"]
    helsinki_id = city_map["Helsinki"]
    dubrovnik_id = city_map["Dubrovnik"]
    oslo_id = city_map["Oslo"]
    madrid_id = city_map["Madrid"]
    paris_id = city_map["Paris"]
    
    city_constraints = [
        days_in_city(mykonos_id) == 4,
        days_in_city(krakow_id) == 5,
        days_in_city(vilnius_id) == 2,
        days_in_city(helsinki_id) == 2,
        days_in_city(dubrovnik_id) == 3,
        days_in_city(oslo_id) == 2,
        days_in_city(madrid_id) == 5,
        days_in_city(paris_id) == 2
    ]
    
    mykonos_days = [
        Or(s[14] == mykonos_id, s[15] == mykonos_id),
        Or(s[15] == mykonos_id, s[16] == mykonos_id),
        Or(s[16] == mykonos_id, s[17] == mykonos_id),
        Or(s[17] == mykonos_id, s[18] == mykonos_id)
    ]
    
    dubrovnik_days = [
        Or(s[1] == dubrovnik_id, s[2] == dubrovnik_id),
        Or(s[2] == dubrovnik_id, s[3] == dubrovnik_id),
        Or(s[3] == dubrovnik_id, s[4] == dubrovnik_id)
    ]
    
    oslo_meeting = Or(Or(s[0] == oslo_id, s[1] == oslo_id), Or(s[1] == oslo_id, s[2] == oslo_id))
    
    solver = Solver()
    solver.add(domain_constraints)
    solver.add(flight_constraints)
    solver.add(city_constraints)
    solver.add(mykonos_days)
    solver.add(dubrovnik_days)
    solver.add(oslo_meeting)
    
    if solver.check() == sat:
        model = solver.model()
        s_val = [model.evaluate(s_i).as_long() for s_i in s]
        
        itinerary = []
        for day in range(1, 19):
            idx0 = s_val[day-1]
            idx1 = s_val[day]
            cities_today = set([cities[idx0], cities[idx1]])
            for city in cities_today:
                itinerary.append({"day": day, "city": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()