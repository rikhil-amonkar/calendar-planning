from z3 import *
import json

def main():
    cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]
    n = 8
    req_days = [2, 5, 4, 4, 4, 3, 2, 3]
    cidx = {city: idx for idx, city in enumerate(cities)}
    
    edges_list = [
        ("Reykjavik", "Munich"),
        ("Munich", "Frankfurt"),
        ("Split", "Oslo"),
        ("Reykjavik", "Oslo"),
        ("Bucharest", "Munich"),
        ("Oslo", "Frankfurt"),
        ("Bucharest", "Barcelona"),
        ("Barcelona", "Frankfurt"),
        ("Reykjavik", "Frankfurt"),
        ("Barcelona", "Stockholm"),
        ("Barcelona", "Reykjavik"),
        ("Stockholm", "Reykjavik"),
        ("Barcelona", "Split"),
        ("Bucharest", "Oslo"),
        ("Bucharest", "Frankfurt"),
        ("Split", "Stockholm"),
        ("Barcelona", "Oslo"),
        ("Stockholm", "Munich"),
        ("Stockholm", "Oslo"),
        ("Split", "Frankfurt"),
        ("Barcelona", "Munich"),
        ("Stockholm", "Frankfurt"),
        ("Munich", "Oslo"),
        ("Split", "Munich")
    ]
    
    edges = set()
    for a, b in edges_list:
        i1 = cidx[a]
        i2 = cidx[b]
        edges.add((i1, i2))
        edges.add((i2, i1))
    
    s = Solver()
    
    T = [Int(f'T_{i}') for i in range(9)]
    s.add(T[0] == 1)
    s.add(T[8] == 20)
    for i in range(1, 8):
        s.add(T[i] >= 1, T[i] <= 20)
    for i in range(8):
        s.add(T[i] <= T[i+1])
    
    which_city = [Int(f'city_pos_{i}') for i in range(8)]
    for i in range(8):
        s.add(which_city[i] >= 0, which_city[i] < 8)
    s.add(Distinct(which_city))
    
    for i in range(8):
        city_index = which_city[i]
        s.add(T[i+1] - T[i] + 1 == req_days[city_index])
    
    for i in range(8):
        s.add(If(which_city[i] == cidx["Oslo"], And(T[i] <= 16, T[i+1] >= 17)))
        s.add(If(which_city[i] == cidx["Reykjavik"], And(T[i] <= 13, T[i+1] >= 9)))
        s.add(If(which_city[i] == cidx["Munich"], And(T[i] <= 16, T[i+1] >= 13)))
        s.add(If(which_city[i] == cidx["Frankfurt"], T[i+1] >= 17))
    
    for i in range(7):
        c1 = which_city[i]
        c2 = which_city[i+1]
        edge_conds = []
        for (a, b) in edges:
            edge_conds.append(And(c1 == a, c2 == b))
        s.add(Or(edge_conds))
    
    if s.check() == sat:
        m = s.model()
        T_vals = [m.evaluate(T[i]).as_long() for i in range(9)]
        city_vals = [m.evaluate(which_city[i]).as_long() for i in range(8)]
        
        itinerary = []
        for i in range(8):
            city_index = city_vals[i]
            city_name = cities[city_index]
            start = T_vals[i]
            end = T_vals[i+1]
            days_list = list(range(start, end + 1))
            itinerary.append({"city": city_name, "days": days_list})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()