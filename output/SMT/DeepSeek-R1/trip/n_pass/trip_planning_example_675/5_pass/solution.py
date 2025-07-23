import z3
import json

def main():
    CitySort, (DUB, SPL, MIL, POR, KRA, MUN) = z3.EnumSort('City', ['DUB', 'SPL', 'MIL', 'POR', 'KRA', 'MUN'])
    
    allowed_pairs = [
        (MUN, POR), (POR, MUN),
        (SPL, MIL), (MIL, SPL),
        (MIL, POR), (POR, MIL),
        (MUN, KRA), (KRA, MUN),
        (MUN, MIL), (MIL, MUN),
        (DUB, MUN), (MUN, DUB),
        (KRA, SPL), (SPL, KRA),
        (KRA, MIL), (MIL, KRA),
        (MUN, SPL), (SPL, MUN)
    ]
    
    solver = z3.Solver()
    
    s = [z3.Const(f's_{i}', CitySort) for i in range(16)]
    f = [z3.Bool(f'f_{i}') for i in range(15)]
    
    for i in range(15):
        flight_possible = z3.Or([z3.And(s[i] == a, s[i+1] == b) for a, b in allowed_pairs])
        solver.add(z3.Implies(f[i], z3.And(s[i] != s[i+1], flight_possible)))
        solver.add(z3.Implies(z3.Not(f[i]), s[i] == s[i+1]))
    
    required_days = {
        DUB: 4,
        SPL: 3,
        MIL: 3,
        POR: 4,
        KRA: 2,
        MUN: 5
    }
    
    for city, req in required_days.items():
        base = z3.Sum([z3.If(s[i] == city, 1, 0) for i in range(16)])
        bonus = z3.Sum([z3.If(z3.And(f[i], s[i+1] == city), 1, 0) for i in range(15)])
        solver.add(base + bonus == req)
    
    solver.add(s[10] == MIL)  # Day 11
    solver.add(s[11] == MIL)  # Day 12
    solver.add(s[12] == MIL)  # Day 13
    solver.add(s[7] == KRA)   # Day 8
    solver.add(s[8] == KRA)   # Day 9
    solver.add(z3.Or([s[i] == MUN for i in range(3, 8)]))  # Days 4-8
    
    if solver.check() == z3.sat:
        model = solver.model()
        s_val = [model.eval(s_i) for s_i in s]
        f_val = [model.eval(f_i) for f_i in f]
        city_names = [val.decl().name() for val in s_val]
        
        segments = []
        start = 0
        current_city = city_names[0]
        
        for i in range(1, 16):
            if z3.is_true(f_val[i-1]):
                segments.append({'day_range': f'Day {start+1}-{i}', 'place': current_city})
                segments.append({'day_range': f'Day {i}-{i}', 'place': city_names[i]})
                start = i
                current_city = city_names[i]
        segments.append({'day_range': f'Day {start+1}-16', 'place': current_city})
        
        result = {'itinerary': segments}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()