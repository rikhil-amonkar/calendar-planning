from z3 import *

def main():
    cities = ["Reykjavik", "Stockholm", "Porto", "Nice", "Venice", "Vienna", "Split", "Copenhagen"]
    durations = [2, 2, 5, 3, 4, 3, 3, 2]
    
    flight_list = [
        ("Copenhagen", "Vienna"),
        ("Nice", "Stockholm"),
        ("Split", "Copenhagen"),
        ("Nice", "Reykjavik"),
        ("Nice", "Porto"),
        ("Reykjavik", "Vienna"),
        ("Stockholm", "Copenhagen"),
        ("Nice", "Venice"),
        ("Nice", "Vienna"),
        ("Reykjavik", "Copenhagen"),
        ("Nice", "Copenhagen"),
        ("Stockholm", "Vienna"),
        ("Venice", "Vienna"),
        ("Copenhagen", "Porto"),
        ("Reykjavik", "Stockholm"),
        ("Stockholm", "Split"),
        ("Split", "Vienna"),
        ("Copenhagen", "Venice"),
        ("Vienna", "Porto")
    ]
    
    name_to_index = {city: idx for idx, city in enumerate(cities)}
    flight_set = set()
    for a, b in flight_list:
        i = name_to_index[a]
        j = name_to_index[b]
        flight_set.add((min(i, j), max(i, j)))
    
    s = Solver()
    s.set("timeout", 30000)  # 30 seconds timeout

    durations_arr = Array('durations_arr', IntSort(), IntSort())
    for i in range(8):
        durations_arr = Store(durations_arr, i, durations[i])
    
    path = IntVector('path', 8)
    start_vars = [Int(f'start_{i}') for i in range(8)]
    end_vars = [start_vars[i] + durations[i] - 1 for i in range(8)]
    
    for i in range(8):
        s.add(path[i] >= 0, path[i] < 8)
    s.add(Distinct(path))
    
    s.add(start_vars[path[0]] == 1)
    
    for i in range(7):
        a = path[i]
        b = path[i+1]
        s.add(start_vars[b] >= start_vars[a])
        s.add(start_vars[b] <= start_vars[a] + Select(durations_arr, a) - 1)
        flight_cons = []
        for edge in flight_set:
            flight_cons.append(And(a == edge[0], b == edge[1]))
            flight_cons.append(And(a == edge[1], b == edge[0]))
        s.add(Or(flight_cons))
    
    s.add([end <= 17 for end in end_vars])
    s.add(Or([end == 17 for end in end_vars]))
    
    s.add(start_vars[0] <= 4, end_vars[0] >= 3)
    s.add(start_vars[1] <= 5, end_vars[1] >= 4)
    s.add(end_vars[2] >= 13)
    s.add(start_vars[5] <= 13, end_vars[5] >= 11)
    
    for i in range(8):
        s.add(start_vars[i] >= 1, start_vars[i] <= 17)
    
    if s.check() == sat:
        m = s.model()
        path_order = []
        for i in range(8):
            city_index = m.evaluate(path[i], model_completion=True).as_long()
            path_order.append((city_index, cities[city_index]))
        start_days = [m.evaluate(start_vars[i], model_completion=True).as_long() for i in range(8)]
        
        print("Travel Itinerary in order of visit:")
        for i, (idx, city) in enumerate(path_order):
            start = start_days[idx]
            end = start + durations[idx] - 1
            print(f"From day {start} to day {end}: stay in {city}")
        
        print("\nDetailed schedule per city:")
        for idx, city in enumerate(cities):
            start = start_days[idx]
            end = start + durations[idx] - 1
            print(f"{city}: day {start} to day {end}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()