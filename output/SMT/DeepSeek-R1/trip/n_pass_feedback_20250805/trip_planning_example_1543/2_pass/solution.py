from z3 import *
import json

def main():
    # Fixed cities with their fixed schedules
    fixed_cities = {
        "Prague": (1, 3),
        "London": (3, 5),
        "Lisbon": (5, 9),
        "Porto": (16, 20),
        "Warsaw": (20, 23)
    }
    
    # Free cities with their required days
    free_cities = {
        "Dublin": 3,
        "Athens": 3,
        "Vilnius": 4,
        "Seville": 2,
        "Dubrovnik": 3
    }
    free_city_names = list(free_cities.keys())
    
    # Direct flight graph (undirected)
    given_edges = [
        ("Warsaw", "Vilnius"),
        ("Prague", "Athens"),
        ("London", "Lisbon"),
        ("Lisbon", "Porto"),
        ("Prague", "Lisbon"),
        ("London", "Dublin"),
        ("Athens", "Vilnius"),
        ("Athens", "Dublin"),
        ("Prague", "London"),
        ("London", "Warsaw"),
        ("Dublin", "Seville"),
        ("Seville", "Porto"),
        ("Lisbon", "Athens"),
        ("Dublin", "Porto"),
        ("Athens", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Porto", "Warsaw"),
        ("Prague", "Warsaw"),
        ("Prague", "Dublin"),
        ("Athens", "Dubrovnik"),
        ("Lisbon", "Dublin"),
        ("Dubrovnik", "Dublin"),
        ("Lisbon", "Seville"),
        ("London", "Athens")
    ]
    graph_set = set()
    for a, b in given_edges:
        graph_set.add((a, b))
        graph_set.add((b, a))
    
    i = Int('i')
    s = Solver()
    s.add(i >= 3, i <= 8)
    n1 = i - 3
    n2 = 8 - i
    
    group = {}
    order = {}
    for city in free_city_names:
        group[city] = Int(f'group_{city}')
        s.add(Or(group[city] == 0, group[city] == 1))
        order[city] = Int(f'order_{city}')
    
    count_group0 = Sum([If(group[city] == 0, 1, 0) for city in free_city_names])
    count_group1 = Sum([If(group[city] == 1, 1, 0) for city in free_city_names])
    s.add(count_group0 == n1)
    s.add(count_group1 == n2)
    
    sum_group0 = Sum([If(group[city] == 0, free_cities[city], 0) for city in free_city_names])
    sum_group1 = Sum([If(group[city] == 1, free_cities[city], 0) for city in free_city_names])
    s.add(sum_group0 == 7 + n1)
    s.add(sum_group1 == 3 + n2)
    
    for city in free_city_names:
        s.add(If(group[city] == 0, And(order[city] >= 0, order[city] < n1), True))
        s.add(If(group[city] == 1, And(order[city] >= 0, order[city] < n2), True))
    
    for i1 in range(len(free_city_names)):
        for j in range(i1 + 1, len(free_city_names)):
            c1 = free_city_names[i1]
            c2 = free_city_names[j]
            s.add(If(And(group[c1] == 0, group[c2] == 0), order[c1] != order[c2], True))
            s.add(If(And(group[c1] == 1, group[c2] == 1), order[c1] != order[c2], True))
    
    if n1 > 0:
        first_in_gap1 = []
        for city in free_city_names:
            if ('Lisbon', city) in graph_set:
                first_in_gap1.append(And(group[city] == 0, order[city] == 0))
        s.add(Or(first_in_gap1))
        
        last_in_gap1 = []
        for city in free_city_names:
            if (city, 'Porto') in graph_set:
                last_in_gap1.append(And(group[city] == 0, order[city] == n1 - 1))
        s.add(Or(last_in_gap1))
        
        for j in range(0, 4):
            cond = j < n1 - 1
            consecutive = []
            for c1 in free_city_names:
                for c2 in free_city_names:
                    if c1 != c2 and (c1, c2) in graph_set:
                        consecutive.append(And(
                            group[c1] == 0,
                            group[c2] == 0,
                            order[c1] == j,
                            order[c2] == j + 1
                        ))
            if consecutive:
                s.add(If(cond, Or(consecutive), True))
    
    if n2 > 0:
        first_in_gap2 = []
        for city in free_city_names:
            if ('Warsaw', city) in graph_set:
                first_in_gap2.append(And(group[city] == 1, order[city] == 0))
        s.add(Or(first_in_gap2))
        
        for j in range(0, 4):
            cond = j < n2 - 1
            consecutive = []
            for c1 in free_city_names:
                for c2 in free_city_names:
                    if c1 != c2 and (c1, c2) in graph_set:
                        consecutive.append(And(
                            group[c1] == 1,
                            group[c2] == 1,
                            order[c1] == j,
                            order[c2] == j + 1
                        ))
            if consecutive:
                s.add(If(cond, Or(consecutive), True))
    
    if s.check() == sat:
        m = s.model()
        i_val = m[i].as_long()
        n1_val = i_val - 3
        n2_val = 8 - i_val
        
        group_assign = {}
        order_assign = {}
        for city in free_city_names:
            group_assign[city] = m[group[city]].as_long()
            order_assign[city] = m[order[city]].as_long()
        
        gap1_cities = []
        gap2_cities = []
        for city in free_city_names:
            if group_assign[city] == 0:
                gap1_cities.append((city, order_assign[city]))
            else:
                gap2_cities.append((city, order_assign[city]))
        
        gap1_cities_sorted = sorted(gap1_cities, key=lambda x: x[1])
        gap2_cities_sorted = sorted(gap2_cities, key=lambda x: x[1])
        
        itinerary = []
        
        # Fixed stays: Prague, London, Lisbon
        for day in range(1, 4):
            itinerary.append(("Prague", day))
        for day in range(3, 6):
            itinerary.append(("London", day))
        for day in range(5, 10):
            itinerary.append(("Lisbon", day))
        
        # Gap1: free cities from day9 to day16
        current_day = 9
        for city, _ in gap1_cities_sorted:
            duration = free_cities[city]
            for d in range(duration):
                itinerary.append((city, current_day + d))
            current_day += duration - 1
        
        # Porto and Warsaw
        for day in range(16, 21):
            itinerary.append(("Porto", day))
        for day in range(20, 24):
            itinerary.append(("Warsaw", day))
        
        # Gap2: free cities from day23 to day26
        current_day = 23
        for city, _ in gap2_cities_sorted:
            duration = free_cities[city]
            for d in range(duration):
                itinerary.append((city, current_day + d))
            current_day += duration - 1
        
        # Create the day-place mappings for JSON
        result_list = []
        for place, day in itinerary:
            result_list.append({"day": day, "place": place})
        
        result_dict = {
            "itinerary": result_list
        }
        print(json.dumps(result_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()