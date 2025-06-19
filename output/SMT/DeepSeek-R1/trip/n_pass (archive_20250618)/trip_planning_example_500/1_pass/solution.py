from z3 import *

def main():
    s = Solver()
    
    city_names = ['Hamburg', 'Munich', 'Manchester', 'Lyon', 'Split']
    lyon_index = city_names.index('Lyon')
    manchester_index = city_names.index('Manchester')
    hamburg_index = city_names.index('Hamburg')
    munich_index = city_names.index('Munich')
    split_index = city_names.index('Split')
    
    c0, c1, c2, c3 = Ints('c0 c1 c2 c3')
    e1, e2, e3 = Ints('e1 e2 e3')
    
    # Durations
    d0 = e1
    d1 = e2 - e1 + 1
    d2 = e3 - e2 + 1
    d3 = 20 - e3  # because the next stay starts at e3 and ends at 19 (since last stay is from 19 to 20)
    d4 = 2  # Manchester from 19 to 20: 2 days
    
    # Constraints on e1, e2, e3
    s.add(e1 >= 1, e1 <= 19)
    s.add(e2 >= e1, e2 <= 19)
    s.add(e3 >= e2, e3 <= 19)
    s.add(Or(e3 == 13, e3 == 14))
    
    # Cities: first four are permutation of [0,1,3,4] (Hamburg, Munich, Lyon, Split), last is Manchester (index2)
    s.add(Distinct(c0, c1, c2, c3))
    for x in [c0, c1, c2, c3]:
        s.add(Or(x == hamburg_index, x == munich_index, x == lyon_index, x == split_index))
    
    # Duration constraints per city
    # For stay0
    s.add(If(c0 == lyon_index, d0 == 2,
            If(c0 == hamburg_index, d0 == 7,
                If(c0 == munich_index, d0 == 6,
                    d0 == 7))))  # Split
    
    # For stay1
    s.add(If(c1 == lyon_index, d1 == 2,
            If(c1 == hamburg_index, d1 == 7,
                If(c1 == munich_index, d1 == 6,
                    d1 == 7))))
    
    # For stay2
    s.add(If(c2 == lyon_index, d2 == 2,
            If(c2 == hamburg_index, d2 == 7,
                If(c2 == munich_index, d2 == 6,
                    d2 == 7))))
    
    # For stay3
    s.add(If(c3 == lyon_index, d3 == 2,
            If(c3 == hamburg_index, d3 == 7,
                If(c3 == munich_index, d3 == 6,
                    d3 == 7))))
    
    # Lyon cannot be in stay3 (since d3 is 7 or 6, not 2)
    s.add(c3 != lyon_index)
    # Lyon must be in one of the first three stays
    s.add(Or(c0 == lyon_index, c1 == lyon_index, c2 == lyon_index))
    
    # Flight constraints
    allowed_strings = [
        ('Split', 'Munich'), ('Munich', 'Split'),
        ('Munich', 'Manchester'), ('Manchester', 'Munich'),
        ('Hamburg', 'Manchester'), ('Manchester', 'Hamburg'),
        ('Hamburg', 'Munich'), ('Munich', 'Hamburg'),
        ('Split', 'Lyon'), ('Lyon', 'Split'),
        ('Lyon', 'Munich'), ('Munich', 'Lyon'),
        ('Hamburg', 'Split'), ('Split', 'Hamburg'),
        ('Manchester', 'Split')
    ]
    allowed_indices = set()
    for a, b in allowed_strings:
        a_idx = city_names.index(a)
        b_idx = city_names.index(b)
        allowed_indices.add((a_idx, b_idx))
    
    flights = [(c0, c1), (c1, c2), (c2, c3), (c3, manchester_index)]
    for (from_city, to_city) in flights:
        constraints = []
        for (a, b) in allowed_indices:
            constraints.append(And(from_city == a, to_city == b))
        s.add(Or(constraints))
    
    if s.check() == sat:
        m = s.model()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()
        c0_val = m[c0].as_long()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        
        city0 = city_names[c0_val]
        city1 = city_names[c1_val]
        city2 = city_names[c2_val]
        city3 = city_names[c3_val]
        city4 = "Manchester"
        
        itinerary = []
        # Stay0: from 1 to e1_val
        itinerary.append({"day_range": "Day 1-{}".format(e1_val), "place": city0})
        itinerary.append({"day_range": "Day {}".format(e1_val), "place": city0})
        itinerary.append({"day_range": "Day {}".format(e1_val), "place": city1})
        # Stay1: from e1_val to e2_val
        itinerary.append({"day_range": "Day {}-{}".format(e1_val, e2_val), "place": city1})
        itinerary.append({"day_range": "Day {}".format(e2_val), "place": city1})
        itinerary.append({"day_range": "Day {}".format(e2_val), "place": city2})
        # Stay2: from e2_val to e3_val
        itinerary.append({"day_range": "Day {}-{}".format(e2_val, e3_val), "place": city2})
        itinerary.append({"day_range": "Day {}".format(e3_val), "place": city2})
        itinerary.append({"day_range": "Day {}".format(e3_val), "place": city3})
        # Stay3: from e3_val to 19
        itinerary.append({"day_range": "Day {}-19".format(e3_val), "place": city3})
        itinerary.append({"day_range": "Day 19", "place": city3})
        itinerary.append({"day_range": "Day 19", "place": "Manchester"})
        # Stay4: from 19 to 20
        itinerary.append({"day_range": "Day 19-20", "place": "Manchester"})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()