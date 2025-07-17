from z3 import *
import json

def main():
    cities = ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    
    durations_arr = [2, 3, 2, 5, 2, 3, 4]  # Riga, Frankfurt, Amsterdam, Vilnius, London, Stockholm, Bucharest
    
    edges_str = [
        ('London', 'Amsterdam'),
        ('Vilnius', 'Frankfurt'),
        ('Riga', 'Vilnius'),
        ('Riga', 'Stockholm'),
        ('London', 'Bucharest'),
        ('Amsterdam', 'Stockholm'),
        ('Amsterdam', 'Frankfurt'),
        ('Frankfurt', 'Stockholm'),
        ('Bucharest', 'Riga'),
        ('Amsterdam', 'Riga'),
        ('Amsterdam', 'Bucharest'),
        ('Riga', 'Frankfurt'),
        ('Bucharest', 'Frankfurt'),
        ('London', 'Frankfurt'),
        ('London', 'Stockholm'),
        ('Amsterdam', 'Vilnius')
    ]
    
    graph_edges_set = set()
    for (a, b) in edges_str:
        i = city_to_int[a]
        j = city_to_int[b]
        graph_edges_set.add((i, j))
        graph_edges_set.add((j, i))
    
    s = Solver()
    
    # City sequence variables
    c = [Int(f'c_{i}') for i in range(7)]
    s_start = [Int(f's_{i}') for i in range(7)]
    s_end = [Int(f'e_{i}') for i in range(7)]
    
    # Distinct cities
    s.add(Distinct(c))
    for i in range(7):
        s.add(c[i] >= 0, c[i] < 7)
    
    # Function to get duration for a city variable
    def get_duration(city_var):
        return If(city_var == 0, 2,
               If(city_var == 1, 3,
               If(city_var == 2, 2,
               If(city_var == 3, 5,
               If(city_var == 4, 2,
               If(city_var == 5, 3, 4))))))
    
    d = [get_duration(c[i]) for i in range(7)]
    
    # Start and end day constraints
    s.add(s_start[0] == 1)
    s.add(s_end[0] == s_start[0] + d[0] - 1)
    
    for i in range(1, 7):
        s.add(s_start[i] == s_end[i-1])
        s.add(s_end[i] == s_start[i] + d[i] - 1)
    
    s.add(s_end[6] == 15)
    
    # Flight constraints: consecutive cities must be connected by a direct flight
    for i in range(6):
        constraints = []
        for edge in graph_edges_set:
            constraints.append(And(c[i] == edge[0], c[i+1] == edge[1]))
        s.add(Or(constraints))
    
    # Event constraints
    for i in range(7):
        # Amsterdam must include day 3 (ensuring either day 2 or 3 is covered)
        s.add(If(c[i] == 2, And(s_start[i] <= 3, s_end[i] >= 3), True))
        # Vilnius must include day 9 (ensuring at least one day between 7 and 11)
        s.add(If(c[i] == 3, And(s_start[i] <= 9, s_end[i] >= 9), True))
        # Stockholm must include at least one day between 13 and 15
        s.add(If(c[i] == 5, And(s_start[i] <= 15, s_end[i] >= 13), True))
    
    if s.check() == sat:
        m = s.model()
        c_val = [m.eval(c_i).as_long() for c_i in c]
        s_val = [m.eval(s_i).as_long() for s_i in s_start]
        e_val = [m.eval(e_i).as_long() for e_i in s_end]
        
        itinerary_list = []
        for i in range(7):
            city_name = cities[c_val[i]]
            start = s_val[i]
            end = e_val[i]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range_str, "place": city_name})
            
            if i < 6:
                itinerary_list.append({"day_range": f"Day {end}", "place": city_name})
                next_city = cities[c_val[i+1]]
                itinerary_list.append({"day_range": f"Day {end}", "place": next_city})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()