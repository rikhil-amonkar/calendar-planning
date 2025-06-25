from z3 import *
import json

def main():
    # City indices
    cities = {
        "Prague": 0,
        "Tallinn": 1,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 4,
        "Milan": 5,
        "Lisbon": 6,
        "Santorini": 7,
        "Riga": 8,
        "Stockholm": 9
    }
    city_names = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
    
    # Required days per city (in order of index: 0 to 9)
    req_array = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]
    adjusted_req = [r - 1 for r in req_array]  # Adjusted for flight days
    
    # Directed flight edges
    edges = []
    edges.append((8, 0)); edges.append((0, 8))  # Riga and Prague
    edges.append((9, 5)); edges.append((5, 9))  # Stockholm and Milan
    edges.append((8, 5)); edges.append((5, 8))  # Riga and Milan
    edges.append((6, 9)); edges.append((9, 6))  # Lisbon and Stockholm
    edges.append((9, 7))  # from Stockholm to Santorini
    edges.append((4, 2)); edges.append((2, 4))  # Naples and Warsaw
    edges.append((6, 2)); edges.append((2, 6))  # Lisbon and Warsaw
    edges.append((4, 5)); edges.append((5, 4))  # Naples and Milan
    edges.append((6, 4)); edges.append((4, 6))  # Lisbon and Naples
    edges.append((8, 1))  # from Riga to Tallinn
    edges.append((1, 0)); edges.append((0, 1))  # Tallinn and Prague
    edges.append((9, 2)); edges.append((2, 9))  # Stockholm and Warsaw
    edges.append((8, 2)); edges.append((2, 8))  # Riga and Warsaw
    edges.append((6, 8)); edges.append((8, 6))  # Lisbon and Riga
    edges.append((8, 9)); edges.append((9, 8))  # Riga and Stockholm
    edges.append((6, 3)); edges.append((3, 6))  # Lisbon and Porto
    edges.append((6, 0)); edges.append((0, 6))  # Lisbon and Prague
    edges.append((5, 3)); edges.append((3, 5))  # Milan and Porto
    edges.append((0, 5)); edges.append((5, 0))  # Prague and Milan
    edges.append((6, 5)); edges.append((5, 6))  # Lisbon and Milan
    edges.append((2, 3)); edges.append((3, 2))  # Warsaw and Porto
    edges.append((2, 1)); edges.append((1, 2))  # Warsaw and Tallinn
    edges.append((7, 5)); edges.append((5, 7))  # Santorini and Milan
    edges.append((9, 0)); edges.append((0, 9))  # Stockholm and Prague
    edges.append((9, 1)); edges.append((1, 9))  # Stockholm and Tallinn
    edges.append((2, 5)); edges.append((5, 2))  # Warsaw and Milan
    edges.append((7, 4)); edges.append((4, 7))  # Santorini and Naples
    edges.append((2, 0)); edges.append((0, 2))  # Warsaw and Prague

    s = Solver()
    
    # Sequence of 10 cities
    seq = [Int('s%d' % i) for i in range(10)]
    for i in range(10):
        s.add(seq[i] >= 0, seq[i] <= 9)
    s.add(Distinct(seq))
    
    # Cumulative sums: 11 elements (0 to 10)
    cum_sum = [Int('cum%d' % i) for i in range(11)]
    s.add(cum_sum[0] == 0)
    
    # Define adjusted_req for each position in the sequence
    for i in range(10):
        a_i = Int('a%d' % i)
        conds = []
        for c in range(10):
            conds.append(And(seq[i] == c, a_i == adjusted_req[c]))
        s.add(Or(conds))
        s.add(cum_sum[i+1] == cum_sum[i] + a_i)
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(9):
        edge_conds = []
        for e in edges:
            edge_conds.append(And(seq[i] == e[0], seq[i+1] == e[1]))
        s.add(Or(edge_conds))
    
    # Riga constraint: must start on day 5 -> cum_sum at its index must be 4
    riga_constraint = []
    for i in range(10):
        riga_constraint.append(And(seq[i] == 8, cum_sum[i] == 4))
    s.add(Or(riga_constraint))
    
    # Tallinn constraint: must have at least one day in [18,20] -> start in [16,20]
    tallinn_constraint = []
    for i in range(10):
        tallinn_constraint.append(And(seq[i] == 1, cum_sum[i] >= 15, cum_sum[i] <= 19))
    s.add(Or(tallinn_constraint))
    
    # Milan constraint: must have at least one day in [24,26] -> start in [22,26]
    milan_constraint = []
    for i in range(10):
        milan_constraint.append(And(seq[i] == 5, cum_sum[i] >= 21, cum_sum[i] <= 25))
    s.add(Or(milan_constraint))
    
    if s.check() == sat:
        m = s.model()
        sol_seq = [m.evaluate(seq[i]).as_long() for i in range(10)]
        sol_cum_sum = [m.evaluate(cum_sum[i]).as_long() for i in range(11)]
        
        itinerary = []
        for i in range(10):
            city_idx = sol_seq[i]
            city_name = city_names[city_idx]
            start_day = 1 + sol_cum_sum[i]
            length = req_array[city_idx]
            end_day = start_day + length - 1
            itinerary.append({"day_range": "Day %d-%d" % (start_day, end_day), "place": city_name})
            if i < 9:
                itinerary.append({"day_range": "Day %d" % end_day, "place": city_name})
                next_city_idx = sol_seq[i+1]
                next_city_name = city_names[next_city_idx]
                itinerary.append({"day_range": "Day %d" % end_day, "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()