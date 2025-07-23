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
        start_days = {}
        end_days = {}
        current_city = model.eval(s[0]).decl().name()
        start_day = 1
        segments = []
        
        for i in range(1, 16):
            city_name = model.eval(s[i]).decl().name()
            flying = z3.is_true(model.eval(f[i-1]))
            
            if flying or city_name != current_city:
                segments.append({
                    'day_range': f'Day {start_day}-{i}',
                    'place': current_city
                })
                if flying:
                    segments.append({
                        'day_range': f'Day {i}',
                        'place': city_name
                    })
                    start_day = i + 1
                else:
                    start_day = i
                current_city = city_name
            elif i == 15:
                segments.append({
                    'day_range': f'Day {start_day}-16',
                    'place': current_city
                })
        
        if len(segments) == 0 or segments[-1]['day_range'] != f'Day {start_day}-16':
            segments.append({
                'day_range': f'Day {start_day}-16',
                'place': current_city
            })
        
        result = {'itinerary': segments}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()