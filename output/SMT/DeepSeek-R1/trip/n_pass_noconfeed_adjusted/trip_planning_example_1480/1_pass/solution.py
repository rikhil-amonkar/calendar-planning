from z3 import *
import json

def main():
    # Cities and their required days
    cities = ['Istanbul', 'Vienna', 'Riga', 'Brussels', 'Madrid', 'Vilnius', 'Venice', 'Geneva', 'Munich', 'Reykjavik']
    req_days = [4, 4, 2, 2, 4, 4, 5, 4, 5, 2]
    
    # Direct flights list
    direct_flights = [
        ('Munich', 'Vienna'),
        ('Istanbul', 'Brussels'),
        ('Vienna', 'Vilnius'),
        ('Madrid', 'Munich'),
        ('Venice', 'Brussels'),
        ('Riga', 'Brussels'),
        ('Geneva', 'Istanbul'),
        ('Munich', 'Reykjavik'),
        ('Vienna', 'Istanbul'),
        ('Riga', 'Istanbul'),
        ('Reykjavik', 'Vienna'),
        ('Venice', 'Munich'),
        ('Madrid', 'Venice'),
        ('Vilnius', 'Istanbul'),
        ('Venice', 'Vienna'),
        ('Venice', 'Istanbul'),
        ('Reykjavik', 'Madrid'),
        ('Riga', 'Munich'),
        ('Munich', 'Istanbul'),
        ('Reykjavik', 'Brussels'),
        ('Vilnius', 'Brussels'),
        ('Vilnius', 'Munich'),
        ('Madrid', 'Vienna'),
        ('Vienna', 'Riga'),
        ('Geneva', 'Vienna'),
        ('Madrid', 'Brussels'),
        ('Vienna', 'Brussels'),
        ('Geneva', 'Brussels'),
        ('Geneva', 'Madrid'),
        ('Munich', 'Brussels'),
        ('Madrid', 'Istanbul'),
        ('Geneva', 'Munich')
    ]
    
    # Create solver instance
    s = Solver()
    
    # Create a 27x10 matrix of booleans: days 1-27, 10 cities
    in_city = [[Bool(f"day_{d}_{c}") for c in cities] for d in range(1, 28)]
    
    # Constraint: Each day must be in at least one city
    for d in range(27):
        s.add(Or([in_city[d][i] for i in range(10)]))
    
    # Constraint: Total days per city must match requirements
    for i, city in enumerate(cities):
        total_days = Sum([If(in_city[d][i], 1, 0) for d in range(27)])
        s.add(total_days == req_days[i])
    
    # Specific constraints
    # Istanbul: 4 days
    # Vienna: 4 days
    # Riga: 2 days
    # Brussels: 2 days, with wedding on day 26-27
    s.add(And([in_city[25][3], in_city[26][3]]))  # Days 26 and 27 in Brussels (index 3)
    # Madrid: 4 days
    # Vilnius: 4 days, with friends between day 20-23
    vilnius_index = cities.index('Vilnius')
    s.add(Or([in_city[d][vilnius_index] for d in range(19, 23)]))  # Days 20-23 inclusive
    # Venice: 5 days, workshop between day 7-11
    venice_index = cities.index('Venice')
    s.add(Or([in_city[d][venice_index] for d in range(6, 11)]))  # Days 7-11 inclusive
    # Geneva: 4 days, relatives between day 1-4
    geneva_index = cities.index('Geneva')
    s.add(And([in_city[0][geneva_index], in_city[1][geneva_index], in_city[2][geneva_index], in_city[3][geneva_index]]))
    # Munich: 5 days
    # Reykjavik: 2 days

    # Travel constraints: If two cities on same day, must have direct flight
    for d in range(27):
        for i in range(10):
            for j in range(i+1, 10):
                both_in = And(in_city[d][i], in_city[d][j])
                connected = Or([And(cities[i] == a, cities[j] == b) for a, b in direct_flights] + 
                              [And(cities[i] == b, cities[j] == a) for a, b in direct_flights])
                s.add(Implies(both_in, connected))
    
    # Continuity constraints
    for d in range(26):
        for i in range(10):
            # If city i not present on day d but present on day d+1, then must have traveled from some city j to i
            left = And(Not(in_city[d][i]), in_city[d+1][i])
            possible_transition = Or([And(in_city[d][j], in_city[d+1][j]) for j in range(10) if i != j])
            s.add(Implies(left, possible_transition))
            
            # If city i present on day d but not on day d+1, then must have traveled from i to some city j
            arrived = And(in_city[d][i], Not(in_city[d+1][i]))
            possible_transition2 = Or([And(in_city[d][j], in_city[d+1][j]) for j in range(10) if i != j])
            s.add(Implies(arrived, possible_transition2))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        schedule = []
        for d in range(27):
            day_cities = []
            for i in range(10):
                if m.evaluate(in_city[d][i]):
                    day_cities.append(cities[i])
            schedule.append(day_cities)
        
        # Group consecutive days with same cities
        itinerary = []
        start_day = 0
        current_places = set(schedule[0])
        for d in range(1, 27):
            if set(schedule[d]) == current_places:
                continue
            else:
                end_day = d - 1
                if start_day == end_day:
                    day_range = f"Day {start_day+1}"
                else:
                    day_range = f"Day {start_day+1}-{end_day+1}"
                itinerary.append({
                    "day_range": day_range,
                    "place": " and ".join(sorted(current_places))
                })
                start_day = d
                current_places = set(schedule[d])
        
        # Add the last segment
        if start_day == 26:
            day_range = f"Day {start_day+1}"
        else:
            day_range = f"Day {start_day+1}-27"
        itinerary.append({
            "day_range": day_range,
            "place": " and ".join(sorted(current_places))
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()