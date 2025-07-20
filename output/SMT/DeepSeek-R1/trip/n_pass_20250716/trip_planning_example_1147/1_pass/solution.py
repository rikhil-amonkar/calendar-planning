from z3 import *

def main():
    # Cities in the middle segment
    cities = ['Brussels', 'Helsinki', 'Split', 'Dubrovnik', 'Milan']
    reqs = [3, 3, 4, 2, 4]  # Corresponding required days

    # Direct flights (undirected)
    flight_list = [
        ('Milan', 'Frankfurt'),
        ('Split', 'Frankfurt'),
        ('Milan', 'Split'),
        ('Brussels', 'Vilnius'),
        ('Brussels', 'Helsinki'),
        ('Istanbul', 'Brussels'),
        ('Milan', 'Vilnius'),
        ('Brussels', 'Milan'),
        ('Istanbul', 'Helsinki'),
        ('Helsinki', 'Vilnius'),
        ('Helsinki', 'Dubrovnik'),
        ('Split', 'Vilnius'),
        ('Dubrovnik', 'Istanbul'),
        ('Istanbul', 'Milan'),
        ('Helsinki', 'Frankfurt'),
        ('Istanbul', 'Vilnius'),
        ('Split', 'Helsinki'),
        ('Milan', 'Helsinki'),
        ('Istanbul', 'Frankfurt'),
        ('Brussels', 'Frankfurt'),
        ('Dubrovnik', 'Frankfurt'),
        ('Frankfurt', 'Vilnius')
    ]
    
    flight_set = set()
    for edge in flight_list:
        flight_set.add(frozenset(edge))
    
    # Precompute connectivity for the middle cities to Istanbul and Frankfurt
    connected_to_Istanbul = [frozenset([city, 'Istanbul']) in flight_set for city in cities]
    connected_to_Frankfurt = [frozenset([city, 'Frankfurt']) in flight_set for city in cities]
    
    # Adjacency matrix for the 5 cities
    adj_matrix_5 = [[False]*5 for _ in range(5)]
    for i in range(5):
        for j in range(5):
            if i != j:
                edge = frozenset([cities[i], cities[j]])
                adj_matrix_5[i][j] = (edge in flight_set)
    
    # Z3 variables
    d1 = Int('d1')
    d2 = Int('d2')
    d3 = Int('d3')
    d4 = Int('d4')
    assign = [Int(f'assign_{i}') for i in range(5)]
    
    s = Solver()
    
    # Flight day constraints
    s.add(d1 >= 5, d1 <= 16)
    s.add(d2 >= d1, d2 <= 16)
    s.add(d3 >= d2, d3 <= 16)
    s.add(d4 >= d3, d4 <= 16)
    
    # Durations
    duration_A = d1 - 4
    duration_B = d2 - d1 + 1
    duration_C = d3 - d2 + 1
    duration_D = d4 - d3 + 1
    duration_E = 17 - d4
    
    # Assignment constraints
    s.add([And(a >= 0, a < 5) for a in assign])
    s.add(Distinct(assign))
    
    # First city connected to Istanbul
    for i in range(5):
        if not connected_to_Istanbul[i]:
            s.add(assign[0] != i)
    
    # Last city connected to Frankfurt
    for i in range(5):
        if not connected_to_Frankfurt[i]:
            s.add(assign[4] != i)
    
    # Consecutive cities connected
    for k in range(4):
        for i in range(5):
            for j in range(5):
                if not adj_matrix_5[i][j]:
                    s.add(Or(assign[k] != i, assign[k+1] != j))
    
    # Duration constraints
    s.add(duration_A == reqs[assign[0]])
    s.add(duration_B == reqs[assign[1]])
    s.add(duration_C == reqs[assign[2]])
    s.add(duration_D == reqs[assign[3]])
    s.add(duration_E == reqs[assign[4]])
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        assign_val = [m.evaluate(a).as_long() for a in assign]
        d1_val = m.evaluate(d1).as_long()
        d2_val = m.evaluate(d2).as_long()
        d3_val = m.evaluate(d3).as_long()
        d4_val = m.evaluate(d4).as_long()
        
        city_names = [cities[i] for i in assign_val]
        city_A, city_B, city_C, city_D, city_E = city_names
        
        itinerary = []
        
        # Istanbul segment
        itinerary.append({"day_range": "Day 1-5", "place": "Istanbul"})
        itinerary.append({"day_range": "Day 5", "place": "Istanbul"})
        itinerary.append({"day_range": "Day 5", "place": city_A})
        itinerary.append({"day_range": f"Day 5-{d1_val}", "place": city_A})
        
        # Flight to B
        itinerary.append({"day_range": f"Day {d1_val}", "place": city_A})
        itinerary.append({"day_range": f"Day {d1_val}", "place": city_B})
        itinerary.append({"day_range": f"Day {d1_val}-{d2_val}", "place": city_B})
        
        # Flight to C
        itinerary.append({"day_range": f"Day {d2_val}", "place": city_B})
        itinerary.append({"day_range": f"Day {d2_val}", "place": city_C})
        itinerary.append({"day_range": f"Day {d2_val}-{d3_val}", "place": city_C})
        
        # Flight to D
        itinerary.append({"day_range": f"Day {d3_val}", "place": city_C})
        itinerary.append({"day_range": f"Day {d3_val}", "place": city_D})
        itinerary.append({"day_range": f"Day {d3_val}-{d4_val}", "place": city_D})
        
        # Flight to E
        itinerary.append({"day_range": f"Day {d4_val}", "place": city_D})
        itinerary.append({"day_range": f"Day {d4_val}", "place": city_E})
        itinerary.append({"day_range": f"Day {d4_val}-16", "place": city_E})
        
        # Flight to Frankfurt
        itinerary.append({"day_range": "Day 16", "place": city_E})
        itinerary.append({"day_range": "Day 16", "place": "Frankfurt"})
        itinerary.append({"day_range": "Day 16-18", "place": "Frankfurt"})
        
        # Flight to Vilnius
        itinerary.append({"day_range": "Day 18", "place": "Frankfurt"})
        itinerary.append({"day_range": "Day 18", "place": "Vilnius"})
        itinerary.append({"day_range": "Day 18-22", "place": "Vilnius"})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print({"itinerary": []})

if __name__ == "__main__":
    main()