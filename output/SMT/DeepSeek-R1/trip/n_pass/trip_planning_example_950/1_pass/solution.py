from z3 import *
import json

def main():
    # City to integer mapping
    city_int = {
        "Rome": 0,
        "Mykonos": 1,
        "Riga": 2,
        "Munich": 3,
        "Bucharest": 4,
        "Nice": 5,
        "Krakow": 6
    }
    int_city = {v: k for k, v in city_int.items()}
    
    # Length of stay for each city
    len_dict = {
        0: 4,  # Rome
        1: 3,  # Mykonos
        2: 3,  # Riga
        3: 4,  # Munich
        4: 4,  # Bucharest
        5: 3,  # Nice
        6: 2   # Krakow
    }
    
    # Define directed flight edges
    bidirectional_pairs = [
        ("Rome", "Nice"), ("Nice", "Rome"),
        ("Rome", "Munich"), ("Munich", "Rome"),
        ("Rome", "Mykonos"), ("Mykonos", "Rome"),
        ("Rome", "Bucharest"), ("Bucharest", "Rome"),
        ("Mykonos", "Nice"), ("Nice", "Mykonos"),
        ("Mykonos", "Munich"), ("Munich", "Mykonos"),
        ("Riga", "Nice"), ("Nice", "Riga"),
        ("Riga", "Bucharest"), ("Bucharest", "Riga"),
        ("Munich", "Bucharest"), ("Bucharest", "Munich"),
        ("Munich", "Nice"), ("Nice", "Munich"),
        ("Munich", "Krakow"), ("Krakow", "Munich")
    ]
    directed_edges = [
        ("Rome", "Riga"),
        ("Riga", "Munich")
    ]
    
    # Create edge set
    edge_set = set()
    for A, B in bidirectional_pairs:
        edge_set.add((city_int[A], city_int[B]))
    for A, B in directed_edges:
        edge_set.add((city_int[A], city_int[B]))
    
    # Z3 variables for permutation indices
    p0, p1, p2, p3, p4 = Ints('p0 p1 p2 p3 p4')
    s = Solver()
    
    # Ensure distinct permutation indices
    s.add(Distinct(p0, p1, p2, p3, p4))
    s.add(p0 >= 0, p0 < 5)
    s.add(p1 >= 0, p1 < 5)
    s.add(p2 >= 0, p2 < 5)
    s.add(p3 >= 0, p3 < 5)
    s.add(p4 >= 0, p4 < 5)
    
    # Mid cities in integer form
    mid_city_ints = [1, 2, 3, 4, 5]  # Mykonos, Riga, Munich, Bucharest, Nice
    
    # Define the city sequence
    s0 = 0  # Rome
    s6 = 6  # Krakow
    
    s1 = If(p0 == 0, mid_city_ints[0],
            If(p0 == 1, mid_city_ints[1],
            If(p0 == 2, mid_city_ints[2],
            If(p0 == 3, mid_city_ints[3],
            mid_city_ints[4]))))
    s2 = If(p1 == 0, mid_city_ints[0],
            If(p1 == 1, mid_city_ints[1],
            If(p1 == 2, mid_city_ints[2],
            If(p1 == 3, mid_city_ints[3],
            mid_city_ints[4]))))
    s3 = If(p2 == 0, mid_city_ints[0],
            If(p2 == 1, mid_city_ints[1],
            If(p2 == 2, mid_city_ints[2],
            If(p2 == 3, mid_city_ints[3],
            mid_city_ints[4]))))
    s4 = If(p3 == 0, mid_city_ints[0],
            If(p3 == 1, mid_city_ints[1],
            If(p3 == 2, mid_city_ints[2],
            If(p3 == 3, mid_city_ints[3],
            mid_city_ints[4]))))
    s5 = If(p4 == 0, mid_city_ints[0],
            If(p4 == 1, mid_city_ints[1],
            If(p4 == 2, mid_city_ints[2],
            If(p4 == 3, mid_city_ints[3],
            mid_city_ints[4]))))
    
    sequence = [s0, s1, s2, s3, s4, s5, s6]
    
    # Flight constraints
    for i in range(6):
        conds = []
        for edge in edge_set:
            conds.append(And(sequence[i] == edge[0], sequence[i+1] == edge[1]))
        s.add(Or(conds))
    
    # Mykonos constraint: must be in Mykonos on at least one day between 4 and 6
    for k in range(1, 6):  # Mykonos can be at positions 1 to 5 in the sequence
        total = 4  # a0 = 1, and the length of Rome is 4, so cumulative without count of Rome is 4
        for j in range(1, k):  # j from 1 to k-1 (city indices in the sequence from 1 to k-1)
            total = total + If(sequence[j] == 1, 3,
                              If(sequence[j] == 2, 3,
                                 If(sequence[j] == 3, 4,
                                    If(sequence[j] == 4, 4, 3))))
        a_k = 1 + total - k
        s.add(If(sequence[k] == 1, And(a_k >= 2, a_k <= 6), True))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        perm = []
        for var in [p0, p1, p2, p3, p4]:
            perm.append(model[var].as_long())
        seq_cities = ["Rome"]
        mid_cities = ["Mykonos", "Riga", "Munich", "Bucharest", "Nice"]
        for idx in perm:
            seq_cities.append(mid_cities[idx])
        seq_cities.append("Krakow")
        
        # Compute arrival days
        a = [1]
        for i in range(1, 7):
            prev_city = seq_cities[i-1]
            a_i = a[i-1] + len_dict[city_int[prev_city]] - 1
            a.append(a_i)
        
        # Generate itinerary: for day d, the city where we are at the end of the day
        itinerary = []
        current_city_idx = 0
        for day in range(1, 18):
            while day >= a[current_city_idx] + len_dict[city_int[seq_cities[current_city_idx]]]:
                current_city_idx += 1
            itinerary.append({"day": day, "place": seq_cities[current_city_idx]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()