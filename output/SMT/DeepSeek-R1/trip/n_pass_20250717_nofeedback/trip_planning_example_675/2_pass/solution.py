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
        total = 0
        for i in range(16):
            if i < 15:
                cond = z3.Or(s[i] == city, z3.And(f[i], s[i+1] == city))
            else:
                cond = (s[i] == city)
            total += z3.If(cond, 1, 0)
        solver.add(total == req)
    
    wedding_constraints = []
    for day in [11, 12, 13]:
        i = day - 1
        cond = z3.Or(s[i] == MIL, z3.And(f[i], s[i+1] == MIL)) if i < 15 else (s[i] == MIL)
        wedding_constraints.append(cond)
    solver.add(z3.Or(wedding_constraints))
    
    meeting_constraints = []
    for day in [8, 9]:
        i = day - 1
        cond = z3.Or(s[i] == KRA, z3.And(f[i], s[i+1] == KRA)) if i < 15 else (s[i] == KRA)
        meeting_constraints.append(cond)
    solver.add(z3.Or(meeting_constraints))
    
    show_constraints = []
    for day in range(4, 9):
        i = day - 1
        cond = z3.Or(s[i] == MUN, z3.And(f[i], s[i+1] == MUN)) if i < 15 else (s[i] == MUN)
        show_constraints.append(cond)
    solver.add(z3.Or(show_constraints))
    
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        for day in range(1, 17):
            idx = day - 1
            if day < 16 and model.eval(f[idx]):
                city1 = model.eval(s[idx]).decl().name()
                city2 = model.eval(s[idx+1]).decl().name()
                cities = [city1, city2]
            else:
                cities = [model.eval(s[idx]).decl().name()]
            itinerary.append({"day": day, "cities": cities})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()