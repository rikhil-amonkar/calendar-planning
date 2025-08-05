from z3 import *
import json

def main():
    City, (dub, frank, krak) = EnumSort('City', ['Dubrovnik', 'Frankfurt', 'Krakow'])
    cities = {dub: "Dubrovnik", frank: "Frankfurt", krak: "Krakow"}
    
    s0 = Const('s0', City)
    s = [Const(f's_{i}', City) for i in range(1, 11)]
    
    direct_flights = [(dub, frank), (frank, dub), (frank, krak), (krak, frank)]
    
    constraints = []
    
    constraints.append(
        If(s0 != s[0],
            Or(
                And(s0 == dub, s[0] == frank),
                And(s0 == frank, s[0] == dub),
                And(s0 == frank, s[0] == krak),
                And(s0 == krak, s[0] == frank)
            ),
            True
        )
    )
    
    for i in range(0, 9):
        constraints.append(
            If(s[i] != s[i+1],
                Or(
                    And(s[i] == dub, s[i+1] == frank),
                    And(s[i] == frank, s[i+1] == dub),
                    And(s[i] == frank, s[i+1] == krak),
                    And(s[i] == krak, s[i+1] == frank)
                ),
                True
            )
        )
    
    count_dub = 0
    count_dub += If(And(s0 == dub, s[0] != dub), 1, 0)
    for i in range(10):
        count_dub += If(s[i] == dub, 1, 0)
    for j in range(1, 10):
        count_dub += If(And(s[j-1] == dub, s[j] != dub), 1, 0)
    constraints.append(count_dub == 7)
    
    count_frank = 0
    count_frank += If(And(s0 == frank, s[0] != frank), 1, 0)
    for i in range(10):
        count_frank += If(s[i] == frank, 1, 0)
    for j in range(1, 10):
        count_frank += If(And(s[j-1] == frank, s[j] != frank), 1, 0)
    constraints.append(count_frank == 3)
    
    count_krak = 0
    count_krak += If(And(s0 == krak, s[0] != krak), 1, 0)
    for i in range(10):
        count_krak += If(s[i] == krak, 1, 0)
    for j in range(1, 10):
        count_krak += If(And(s[j-1] == krak, s[j] != krak), 1, 0)
    constraints.append(count_krak == 2)
    
    inKrakow9 = Or(s[8] == krak, And(s[7] == krak, s[8] != krak))
    inKrakow10 = Or(s[9] == krak, And(s[8] == krak, s[9] != krak))
    constraints.append(Or(inKrakow9, inKrakow10))
    
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        s0_val = model[s0]
        s_vals = [model[s_i] for s_i in s]
        
        itinerary = []
        for day in range(1, 11):
            city_sym = s_vals[day-1]
            city_name = cities[city_sym]
            itinerary.append({"day": day, "city": city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()