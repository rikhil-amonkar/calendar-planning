from z3 import *

def main():
    cities = {"Dubrovnik": 0, "Split": 1, "Milan": 2, "Porto": 3, "Krakow": 4, "Munich": 5}
    rev_cities = {0: "Dubrovnik", 1: "Split", 2: "Milan", 3: "Porto", 4: "Krakow", 5: "Munich"}
    required_days = [4, 3, 3, 4, 2, 5]
    
    flight_list = [
        ("Munich", "Porto"),
        ("Split", "Milan"),
        ("Milan", "Porto"),
        ("Munich", "Krakow"),
        ("Munich", "Milan"),
        ("Dubrovnik", "Munich"),
        ("Krakow", "Split"),
        ("Krakow", "Milan"),
        ("Munich", "Split")
    ]
    flight_pairs = []
    for a, b in flight_list:
        i = cities[a]
        j = cities[b]
        flight_pairs.append((i, j))
        flight_pairs.append((j, i))
    flight_pairs = list(set(flight_pairs))
    
    n = 6
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    city = [Int(f'city_{i}') for i in range(n)]
    
    s = Solver()
    
    for i in range(n):
        s.add(city[i] >= 0, city[i] <= 5)
    s.add(Distinct(city))
    
    s.add(start[0] == 1)
    s.add(end[n-1] == 16)
    
    for i in range(n-1):
        s.add(end[i] == start[i+1])
    
    for i in range(n):
        s.add(end[i] - start[i] + 1 == required_days[city[i]])
    
    for i in range(n):
        s.add(If(city[i] == 5, And(start[i] == 4, end[i] == 8), True))
        s.add(If(city[i] == 4, And(start[i] == 8, end[i] == 9), True))
    
    s.add(Or([And(city[i] == 5, city[i+1] == 4) for i in range(n-1)]))
    
    for i in range(n-1):
        s.add(Or([And(city[i] == a, city[i+1] == b) for (a, b) in flight_pairs]))
    
    if s.check() == sat:
        m = s.model()
        start_val = [m.evaluate(start[i]).as_long() for i in range(n)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(n)]
        city_val = [m.evaluate(city[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            if start_val[i] == end_val[i]:
                dr_str = f"Day {start_val[i]}"
            else:
                dr_str = f"Day {start_val[i]}-{end_val[i]}"
            itinerary.append({"day_range": dr_str, "place": rev_cities[city_val[i]]})
            if i < n-1:
                day_x = end_val[i]
                itinerary.append({"day_range": f"Day {day_x}", "place": rev_cities[city_val[i]]})
                itinerary.append({"day_range": f"Day {day_x}", "place": rev_cities[city_val[i+1]]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()