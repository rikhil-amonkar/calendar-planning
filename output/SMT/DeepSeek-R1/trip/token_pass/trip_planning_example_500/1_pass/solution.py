from z3 import *
import json

def main():
    n_days = 20
    cities = ['Hamburg', 'Munich', 'Manchester', 'Lyon', 'Split']
    req_days = {'Hamburg': 7, 'Munich': 6, 'Manchester': 2, 'Lyon': 2, 'Split': 7}
    
    edges = [
        ('Split', 'Munich'),
        ('Munich', 'Manchester'),
        ('Hamburg', 'Manchester'),
        ('Hamburg', 'Munich'),
        ('Split', 'Lyon'),
        ('Lyon', 'Munich'),
        ('Hamburg', 'Split'),
        ('Manchester', 'Split')
    ]
    
    graph = {}
    for c in cities:
        graph[c] = set()
    for u, v in edges:
        graph[u].add(v)
        graph[v].add(u)
    
    def connected(c1, c2):
        return c2 in graph[c1]
    
    s = Solver()
    
    in_var = {}
    for i in range(1, n_days+1):
        for c in cities:
            in_var[(i, c)] = Bool(f"in_{i}_{c}")
    
    for i in range(1, n_days+1):
        cities_day = [in_var[(i, c)] for c in cities]
        s.add(AtLeast(*cities_day, 1))
        s.add(AtMost(*cities_day, 2))
        
        for c1 in cities:
            for c2 in cities:
                if c1 != c2:
                    s.add(Implies(And(in_var[(i, c1)], in_var[(i, c2)]), connected(c1, c2)))
    
    for i in range(1, n_days):
        common_cities = []
        for c in cities:
            common_cities.append(And(in_var[(i, c)], in_var[(i+1, c)]))
        s.add(Or(common_cities))
    
    for c in cities:
        total = 0
        for i in range(1, n_days+1):
            total += If(in_var[(i, c)], 1, 0)
        s.add(total == req_days[c])
    
    s.add(in_var[(19, 'Manchester')] == True)
    s.add(in_var[(20, 'Manchester')] == True)
    s.add(in_var[(13, 'Lyon')] == True)
    s.add(in_var[(14, 'Lyon')] == True)
    
    if s.check() == sat:
        m = s.model()
        day_cities = []
        for i in range(1, n_days+1):
            cities_i = set()
            for c in cities:
                if is_true(m.evaluate(in_var[(i, c)])):
                    cities_i.add(c)
            day_cities.append(cities_i)
        
        itinerary = []
        start_index = 0
        current_set = day_cities[0]
        for i in range(1, n_days):
            if day_cities[i] == current_set:
                continue
            else:
                end_index = i
                if start_index + 1 == end_index:
                    day_range_str = f"Day {start_index+1}"
                else:
                    day_range_str = f"Day {start_index+1}-{end_index}"
                if len(current_set) == 1:
                    place_str = next(iter(current_set))
                else:
                    place_str = " and ".join(sorted(current_set))
                itinerary.append({"day_range": day_range_str, "place": place_str})
                start_index = i
                current_set = day_cities[i]
        
        end_index = n_days
        if start_index + 1 == end_index:
            day_range_str = f"Day {start_index+1}"
        else:
            day_range_str = f"Day {start_index+1}-{end_index}"
        if len(current_set) == 1:
            place_str = next(iter(current_set))
        else:
            place_str = " and ".join(sorted(current_set))
        itinerary.append({"day_range": day_range_str, "place": place_str})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()