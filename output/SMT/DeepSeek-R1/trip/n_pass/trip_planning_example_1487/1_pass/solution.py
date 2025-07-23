from z3 import *
import json

def main():
    city_names = [
        'Copenhagen',
        'Geneva',
        'Mykonos',
        'Naples',
        'Prague',
        'Dubrovnik',
        'Athens',
        'Santorini',
        'Brussels',
        'Munich'
    ]
    
    req_days = {
        'Copenhagen': 5,
        'Geneva': 3,
        'Mykonos': 2,
        'Naples': 4,
        'Prague': 2,
        'Dubrovnik': 3,
        'Athens': 4,
        'Santorini': 5,
        'Brussels': 4,
        'Munich': 5
    }
    
    req_list = [req_days[city] for city in city_names]
    
    mykonos_index = city_names.index('Mykonos')
    naples_index = city_names.index('Naples')
    copenhagen_index = city_names.index('Copenhagen')
    athens_index = city_names.index('Athens')
    
    flight_strings = [
        "Copenhagen and Dubrovnik",
        "Brussels and Copenhagen",
        "Prague and Geneva",
        "Athens and Geneva",
        "Naples and Dubrovnik",
        "Athens and Dubrovnik",
        "Geneva and Mykonos",
        "Naples and Mykonos",
        "Naples and Copenhagen",
        "Munich and Mykonos",
        "Naples and Athens",
        "Prague and Athens",
        "Santorini and Geneva",
        "Athens and Santorini",
        "Naples and Munich",
        "Prague and Copenhagen",
        "Brussels and Naples",
        "Athens and Mykonos",
        "Athens and Copenhagen",
        "Naples and Geneva",
        "Dubrovnik and Munich",
        "Brussels and Munich",
        "Prague and Brussels",
        "Brussels and Athens",
        "Athens and Munich",
        "Geneva and Munich",
        "Copenhagen and Munich",
        "Brussels and Geneva",
        "Copenhagen and Geneva",
        "Prague and Munich",
        "Copenhagen and Santorini",
        "Naples and Santorini",
        "Geneva and Dubrovnik"
    ]
    
    flight_set = set()
    for flight in flight_strings:
        parts = flight.split(' and ')
        if len(parts) != 2:
            continue
        c1, c2 = parts
        idx1 = city_names.index(c1)
        idx2 = city_names.index(c2)
        flight_set.add((idx1, idx2))
        flight_set.add((idx2, idx1))
    
    s = Solver()
    
    seq = [Int(f'seq_{i}') for i in range(10)]
    
    for i in range(10):
        s.add(seq[i] >= 0, seq[i] < 10)
    
    s.add(Distinct(seq))
    
    s.add(seq[9] == mykonos_index)
    
    s_days = [Int(f's_{i}') for i in range(10)]
    e_days = [Int(f'e_{i}') for i in range(10)]
    
    s.add(s_days[0] == 1)
    for i in range(1, 10):
        s.add(s_days[i] == e_days[i-1])
    s.add(e_days[9] == 28)
    
    req_array = Array('req_array', IntSort(), IntSort())
    for j in range(10):
        s.add(req_array[j] == req_list[j])
    
    for i in range(10):
        s.add(e_days[i] - s_days[i] + 1 == Select(req_array, seq[i]))
    
    for i in range(10):
        is_naples = (seq[i] == naples_index)
        s.add(If(is_naples, And(s_days[i] <= 8, e_days[i] >= 5), True))
        
        is_copenhagen = (seq[i] == copenhagen_index)
        s.add(If(is_copenhagen, And(s_days[i] <= 15, e_days[i] >= 11), True))
        
        is_athens = (seq[i] == athens_index)
        s.add(If(is_athens, And(s_days[i] <= 11, e_days[i] >= 8), True))
    
    for i in range(9):
        constraints = []
        for (a, b) in flight_set:
            constraints.append(And(seq[i] == a, seq[i+1] == b))
        s.add(Or(constraints))
    
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(10)]
        s_days_val = [m.evaluate(s_days[i]).as_long() for i in range(10)]
        e_days_val = [m.evaluate(e_days[i]).as_long() for i in range(10)]
        
        itinerary_list = []
        for day in range(1, 29):
            places = []
            for i in range(10):
                s_day = s_days_val[i]
                e_day = e_days_val[i]
                if day >= s_day and day <= e_day:
                    city_idx = seq_val[i]
                    places.append(city_names[city_idx])
            itinerary_list.append({"day": day, "place": places})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()