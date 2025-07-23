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
    
    solver.add(z3.Or(s[10] == MIL, s[11] == MIL, s[12] == MIL))
    solver.add(z3.Or(s[7] == KRA, s[8] == KRA))
    solver.add(z3.Or([s[i] == MUN for i in range(3, 8)]))
    
    if solver.check() == z3.sat:
        model = solver.model()
        start_idx = 0
        current_city = model.eval(s[0])
        segments = []
        
        for i in range(1, 16):
            city = model.eval(s[i])
            if current_city.eq(city):
                continue
            segments.append({
                'day_range': f'Day {start_idx+1}-{i}',
                'place': current_city.decl().name()
            })
            start_idx = i
            current_city = city
            
        segments.append({
            'day_range': f'Day {start_idx+1}-16',
            'place': current_city.decl().name()
        })
        
        result = {'itinerary': segments}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()