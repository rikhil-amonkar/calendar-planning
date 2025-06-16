from z3 import *

def main():
    cities = ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich', 'Naples']
    
    required_days = {
        'Salzburg': 2,
        'Venice': 5,
        'Bucharest': 4,
        'Brussels': 2,
        'Hamburg': 4,
        'Copenhagen': 4,
        'Nice': 3,
        'Zurich': 5,
        'Naples': 4
    }
    
    flight_str = "Zurich and Brussels, Bucharest and Copenhagen, Venice and Brussels, Nice and Zurich, Hamburg and Nice, Zurich and Naples, Hamburg and Bucharest, Zurich and Copenhagen, Bucharest and Brussels, Hamburg and Brussels, Venice and Naples, Venice and Copenhagen, Bucharest and Naples, Hamburg and Copenhagen, Venice and Zurich, Nice and Brussels, Hamburg and Venice, Copenhagen and Naples, Nice and Naples, Hamburg and Zurich, Salzburg and Hamburg, Zurich and Bucharest, Brussels and Naples, Copenhagen and Brussels, Venice and Nice, Nice and Copenhagen"
    pairs = flight_str.split(', ')
    flight_set = set()
    for p in pairs:
        parts = p.split(' and ')
        if len(parts) == 2:
            c1 = parts[0].strip()
            c2 = parts[1].strip()
            flight_set.add((c1, c2))
            flight_set.add((c2, c1))
    
    neighbors = {}
    for c in cities:
        neighbors[c] = []
        for c2 in cities:
            if c2 == c:
                continue
            if (c, c2) in flight_set:
                neighbors[c].append(c2)
    
    in_vars = { city: [ Bool('in_%s_%d' % (city, d)) for d in range(1, 26) ] for city in cities }
    
    s = Solver()
    
    # C1: Total days per city
    for city in cities:
        total = Sum([If(in_vars[city][d], 1, 0) for d in range(0, 25)])
        s.add(total == required_days[city])
    
    # C2: At least one city per day and at most two cities per day
    for d in range(0, 25):
        s.add(Or([in_vars[city][d] for city in cities]))
        s.add(AtMost(*(in_vars[city][d] for city in cities), 2))
    
    # C3: Travel constraints
    for d in range(1, 25):
        for c in cities:
            current = in_vars[c][d]
            prev = in_vars[c][d-1]
            cond = And(current, Not(prev))
            neighbor_list = neighbors[c]
            if neighbor_list:
                s.add(Implies(cond, Or([in_vars[c2][d-1] for c2 in neighbor_list])))
            else:
                s.add(Not(cond))
    
    # C4: Specific day constraints
    # Brussels: must be on both day 21 and 22
    s.add(in_vars['Brussels'][20])  # day 21
    s.add(in_vars['Brussels'][21])  # day 22
    
    # Copenhagen: at least one day in [18,21] (array indices: 17,18,19,20)
    s.add(Or(in_vars['Copenhagen'][17], in_vars['Copenhagen'][18], in_vars['Copenhagen'][19], in_vars['Copenhagen'][20]))
    
    # Nice: at least one day in [9,11] (array indices: 8,9,10)
    s.add(Or(in_vars['Nice'][8], in_vars['Nice'][9], in_vars['Nice'][10]))
    
    # Naples: at least one day in [22,25] (array indices: 21,22,23,24)
    s.add(Or(in_vars['Naples'][21], in_vars['Naples'][22], in_vars['Naples'][23], in_vars['Naples'][24]))
    
    if s.check() == sat:
        m = s.model()
        print("Day\tCities")
        for d in range(0, 25):
            day_cities = []
            for city in cities:
                if is_true(m.evaluate(in_vars[city][d])):
                    day_cities.append(city)
            print(f"{d+1}\t{', '.join(day_cities)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()