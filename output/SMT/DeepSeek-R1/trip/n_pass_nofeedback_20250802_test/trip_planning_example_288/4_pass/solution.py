from z3 import *

def main():
    manchester = 0
    stuttgart = 1
    madrid = 2
    vienna = 3
    city_names = {0: "Manchester", 1: "Stuttgart", 2: "Madrid", 3: "Vienna"}
    
    city1 = Int('city1')
    city2 = Int('city2')
    city3 = Int('city3')
    city4 = Int('city4')
    e1 = Int('e1')
    e2 = Int('e2')
    e3 = Int('e3')
    
    s = Solver()
    
    edges = [(manchester, stuttgart), (manchester, madrid), (manchester, vienna),
             (stuttgart, vienna), (madrid, vienna)]
    edges_sym = edges + [(j, i) for (i, j) in edges]
    
    len1 = e1
    len2 = e2 - e1 + 1
    len3 = e3 - e2 + 1
    len4 = 15 - e3 + 1
    
    total_manchester = Sum([If(city1 == manchester, len1, 0),
                           If(city2 == manchester, len2, 0),
                           If(city3 == manchester, len3, 0),
                           If(city4 == manchester, len4, 0)])
    total_stuttgart = Sum([If(city1 == stuttgart, len1, 0),
                           If(city2 == stuttgart, len2, 0),
                           If(city3 == stuttgart, len3, 0),
                           If(city4 == stuttgart, len4, 0)])
    total_madrid = Sum([If(city1 == madrid, len1, 0),
                        If(city2 == madrid, len2, 0),
                        If(city3 == madrid, len3, 0),
                        If(city4 == madrid, len4, 0)])
    total_vienna = Sum([If(city1 == vienna, len1, 0),
                        If(city2 == vienna, len2, 0),
                        If(city3 == vienna, len3, 0),
                        If(city4 == vienna, len4, 0)])
    
    s.add(total_manchester == 7)
    s.add(total_stuttgart == 5)
    s.add(total_madrid == 4)
    s.add(total_vienna == 2)
    
    s.add(e1 >= 1, e1 <= 14)
    s.add(e2 > e1, e2 <= 14)
    s.add(e3 > e2, e3 <= 14)
    
    s.add(Or([And(city1 == i, city2 == j) for (i, j) in edges_sym]))
    s.add(Or([And(city2 == i, city3 == j) for (i, j) in edges_sym]))
    s.add(Or([And(city3 == i, city4 == j) for (i, j) in edges_sym]))
    
    for d in range(11, 16):
        is_boundary = Or(d == e1, d == e2, d == e3)
        not_boundary = Not(is_boundary)
        s.add(Or(
            And(d == e1, city2 == stuttgart),
            And(d == e2, city3 == stuttgart),
            And(d == e3, city4 == stuttgart),
            And(not_boundary, 
                Or(
                    And(d <= e1, city1 == stuttgart),
                    And(e1 < d, d < e2, city2 == stuttgart),
                    And(e2 < d, d < e3, city3 == stuttgart),
                    And(d > e3, city4 == stuttgart)
                )
            )
        ))
    
    wedding_conditions = []
    for d in range(1, 8):
        is_boundary = Or(d == e1, d == e2, d == e3)
        not_boundary = Not(is_boundary)
        condition = Or(
            And(is_boundary, 
                Or(
                    And(d == e1, city2 == manchester),
                    And(d == e2, city3 == manchester),
                    And(d == e3, city4 == manchester)
                )
            ),
            And(not_boundary,
                Or(
                    And(d <= e1, city1 == manchester),
                    And(e1 < d, d < e2, city2 == manchester),
                    And(e2 < d, d < e3, city3 == manchester),
                    And(d > e3, city4 == manchester)
                )
            )
        )
        wedding_conditions.append(condition)
    s.add(Or(wedding_conditions))
    
    s.add(Not(And(e1 == 4, e2 == 10, e3 == 11, city1 == madrid, city2 == manchester, city3 == vienna, city4 == stuttgart)))
    
    if s.check() == sat:
        m = s.model()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()
        city1_val = m[city1].as_long()
        city2_val = m[city2].as_long()
        city3_val = m[city3].as_long()
        city4_val = m[city4].as_long()
        
        itinerary = [
            {"day_range": f"Day 1-{e1_val}", "place": city_names[city1_val]},
            {"day_range": f"Day {e1_val}-{e2_val}", "place": city_names[city2_val]},
            {"day_range": f"Day {e2_val}-{e3_val}", "place": city_names[city3_val]},
            {"day_range": f"Day {e3_val}-15", "place": city_names[city4_val]}
        ]
        print('{\n  "itinerary": [')
        for i, item in enumerate(itinerary):
            suffix = "," if i < len(itinerary) - 1 else ""
            print(f'    {{"day_range": "{item["day_range"]}", "place": "{item["place"]}"}}{suffix}')
        print("  ]\n}")
    else:
        print("No valid solution found")

if __name__ == "__main__":
    main()