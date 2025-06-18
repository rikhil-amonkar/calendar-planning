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
            c1, c2 = parts[0].strip(), parts[1].strip()
            flight_set.add((c1, c2))
            flight_set.add((c2, c1))
    
    neighbors = {}
    for c in cities:
        neighbors[c] = set()
        for c2 in cities:
            if c != c2 and (c, c2) in flight_set:
                neighbors[c].add(c2)
    
    in_vars = {city: [Bool(f'in_{city}_{d}') for d in range(25)} for city in cities}
    s = Solver()
    s.set("timeout", 60000)  # 60 second timeout

    # Total days per city
    for city, days in required_days.items():
        s.add(Sum([If(in_vars[city][d], 1, 0) for d in range(25)]) == days)
    
    # At least one city per day, at most two
    for d in range(25):
        s.add(Or([in_vars[city][d] for city in cities]))
        s.add(AtMost(*(in_vars[city][d] for city in cities), 2))
    
    # If two cities on same day, must be connected
    for d in range(25):
        for c1 in cities:
            for c2 in cities:
                if c1 < c2 and c2 not in neighbors[c1]:
                    s.add(Not(And(in_vars[c1][d], in_vars[c2][d])))
    
    # Travel constraints (combined arrival/departure)
    for d in range(1, 25):
        for c in cities:
            # Arrival: If not in city yesterday but here today, must have come from neighbor
            arrive = And(Not(in_vars[c][d-1]), in_vars[c][d])
            if neighbors[c]:
                s.add(Implies(arrive, Or([in_vars[n][d-1] for n in neighbors[c]])))
            else:
                s.add(Not(arrive))
            
            # Departure: If here today but not tomorrow, must go to neighbor today
            if d < 24:
                depart = And(in_vars[c][d], Not(in_vars[c][d+1]))
                if neighbors[c]:
                    s.add(Implies(depart, Or([in_vars[n][d] for n in neighbors[c]])))
    
    # No same two cities consecutive days
    for d in range(24):
        for c1 in cities:
            for c2 in neighbors[c1]:
                if c1 < c2:
                    s.add(Implies(
                        And(in_vars[c1][d], in_vars[c2][d]),
                        Not(And(in_vars[c1][d+1], in_vars[c2][d+1]))
                    ))
    
    # Event windows
    s.add(in_vars['Brussels'][20])  # Day 21
    s.add(in_vars['Brussels'][21])  # Day 22
    s.add(Or([in_vars['Copenhagen'][d] for d in [17, 18, 19, 20]]))  # Days 18-21
    s.add(Or([in_vars['Nice'][d] for d in [8, 9, 10]]))               # Days 9-11
    s.add(Or([in_vars['Naples'][d] for d in [21, 22, 23, 24]]))       # Days 22-25

    if s.check() == sat:
        m = s.model()
        print("Day\tCities")
        for d in range(25):
            present = [city for city in cities if is_true(m.evaluate(in_vars[city][d]))]
            print(f"{d+1}\t{', '.join(present)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()