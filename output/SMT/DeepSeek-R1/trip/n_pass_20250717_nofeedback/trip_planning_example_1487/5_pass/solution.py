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
    
    req_days_list = [req_days[city] for city in city_names]
    
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
    
    req_days_z3 = Array('req_days', IntSort(), IntSort())
    for j in range(10):
        s.add(req_days_z3[j] == req_days_list[j])
    
    for i in range(10):
        dur = req_days_z3[seq[i]]
        s.add(e_days[i] == s_days[i] + dur - 1)
    
    # Event constraints using existential quantification
    naples_constraint = Or([And(seq[i] == naples_index, 
                                s_days[i] <= 8, 
                                e_days[i] >= 5) 
                            for i in range(10)])
    
    copenhagen_constraint = Or([And(seq[i] == copenhagen_index, 
                                   s_days[i] <= 15, 
                                   e_days[i] >= 11) 
                               for i in range(10)])
    
    athens_constraint = Or([And(seq[i] == athens_index, 
                                s_days[i] <= 11, 
                                e_days[i] >= 8) 
                           for i in range(10)])
    
    s.add(naples_constraint, copenhagen_constraint, athens_constraint)
    
    for i in range(9):
        c1 = seq[i]
        c2 = seq[i+1]
        s.add(Or([And(c1 == a, c2 == b) for (a, b) in flight_set]))
    
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(10)]
        s_days_val = [m.evaluate(s_days[i]).as_long() for i in range(10)]
        e_days_val = [m.evaluate(e_days[i]).as_long() for i in range(10)]
        
        itinerary_list = []
        for i in range(10):
            start = s_days_val[i]
            end = e_days_val[i]
            day_range = f"Day {start}-{end}"
            city = city_names[seq_val[i]]
            itinerary_list.append({"day_range": day_range, "place": city})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()