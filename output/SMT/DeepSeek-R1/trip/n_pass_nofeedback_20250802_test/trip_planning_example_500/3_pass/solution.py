from z3 import *
import json

def main():
    City = Datatype('City')
    City.declare('Hamburg')
    City.declare('Munich')
    City.declare('Manchester')
    City.declare('Lyon')
    City.declare('Split')
    City = City.create()
    
    city_map_str = {
        "Hamburg": City.Hamburg,
        "Munich": City.Munich,
        "Manchester": City.Manchester,
        "Lyon": City.Lyon,
        "Split": City.Split
    }
    
    P = [Const(f'P{i}', City) for i in range(0, 21)]
    
    s = Solver()
    
    directed_flights = set()
    bidirectional_edges = [
        ("Split", "Munich"),
        ("Munich", "Manchester"),
        ("Hamburg", "Manchester"),
        ("Hamburg", "Munich"),
        ("Split", "Lyon"),
        ("Lyon", "Munich"),
        ("Hamburg", "Split")
    ]
    unidirectional_edges = [("Manchester", "Split")]
    
    for u, v in bidirectional_edges:
        u_const = city_map_str[u]
        v_const = city_map_str[v]
        directed_flights.add((u_const, v_const))
        directed_flights.add((v_const, u_const))
    
    for u, v in unidirectional_edges:
        u_const = city_map_str[u]
        v_const = city_map_str[v]
        directed_flights.add((u_const, v_const))
    
    for i in range(1, 21):
        prev = P[i-1]
        curr = P[i]
        s.add(If(prev != curr, Or([And(prev == u, curr == v) for (u, v) in directed_flights]), True))
    
    def days_in_city(c):
        return Sum([If(Or(P[i-1] == c, P[i] == c), 1, 0) for i in range(1, 21)])
    
    s.add(days_in_city(City.Hamburg) == 7)
    s.add(days_in_city(City.Munich) == 6)
    s.add(days_in_city(City.Manchester) == 2)
    s.add(days_in_city(City.Lyon) == 2)
    s.add(days_in_city(City.Split) == 7)
    
    s.add(P[13] == City.Lyon)
    for i in range(0, 21):
        if i != 13:
            s.add(P[i] != City.Lyon)
    
    s.add(P[19] == City.Manchester)
    s.add(P[20] == City.Manchester)
    for i in range(1, 21):
        if i != 19 and i != 20:
            s.add(And(P[i-1] != City.Manchester, P[i] != City.Manchester))
    
    if s.check() == sat:
        model = s.model()
        rev_map = {
            City.Hamburg: "Hamburg",
            City.Munich: "Munich",
            City.Manchester: "Manchester",
            City.Lyon: "Lyon",
            City.Split: "Split"
        }
        itinerary = []
        for day in range(1, 21):
            city_val = model[P[day]]
            city_name = rev_map[city_val]
            itinerary.append({"day": day, "place": city_name})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()