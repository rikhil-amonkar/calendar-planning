from z3 import *
import json

def main():
    # Define the parameters
    days = 16
    cities = ['Dublin', 'London', 'Helsinki', 'Reykjavik', 'Mykonos', 'Hamburg']
    required_days = {
        'Mykonos': 3,
        'Reykjavik': 2,
        'Dublin': 5,
        'London': 5,
        'Helsinki': 4,
        'Hamburg': 2
    }
    direct_flights = [
        ('Dublin', 'London'),
        ('Hamburg', 'Dublin'),
        ('Helsinki', 'Reykjavik'),
        ('Hamburg', 'London'),
        ('Dublin', 'Helsinki'),
        ('Reykjavik', 'London'),
        ('London', 'Mykonos'),
        ('Dublin', 'Reykjavik'),
        ('Hamburg', 'Helsinki'),
        ('Helsinki', 'London')
    ]
    direct_flights_set = set()
    for a, b in direct_flights:
        direct_flights_set.add((a, b))
        direct_flights_set.add((b, a))

    # Create the solver
    s = Solver()

    # Create variables: in_city[d][c] is True if we are in city c on day d
    in_city = [[Bool(f"day_{d+1}_{c}") for c in cities] for d in range(days)]

    # Constraint 1: Each day we are in at least one city and at most two cities
    for d in range(days):
        s.add(Or(in_city[d]))
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    s.add(Not(And(in_city[d][i], in_city[d][j], in_city[d][k])))

    # Constraint 2: If two cities on same day, they must have a direct flight
    for d in range(days):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                if (cities[i], cities[j]) not in direct_flights_set:
                    s.add(Not(And(in_city[d][i], in_city[d][j])))

    # Constraint 3: Total days per city
    for c_idx, city in enumerate(cities):
        total = 0
        for d in range(days):
            total += If(in_city[d][c_idx], 1, 0)
        s.add(total == required_days[city])

    # Constraint 4: If in a city on day d+1, must have been in that city or a connected city on day d
    for d in range(days-1):
        for c_idx, city in enumerate(cities):
            other_cities = []
            for c2_idx in range(len(cities)):
                if c2_idx != c_idx and (cities[c2_idx], city) in direct_flights_set:
                    other_cities.append(in_city[d][c2_idx])
            s.add(Implies(in_city[d+1][c_idx], Or(in_city[d][c_idx], Or(other_cities))))

    # Specific constraints
    # Reykjavik wedding between day 9 and 10
    s.add(Or(in_city[8][cities.index('Reykjavik')], in_city[9][cities.index('Reykjavik')]))
    # Dublin show from day 2 to 6
    s.add(Or([in_city[d][cities.index('Dublin')] for d in range(1, 6)]))
    # Hamburg friends between day 1 and 2
    s.add(Or(in_city[0][cities.index('Hamburg')], in_city[1][cities.index('Hamburg')]))

    # Check and get the model
    if s.check() == sat:
        m = s.model()
        assignment = []
        for d in range(days):
            cities_today = []
            for c_idx, city in enumerate(cities):
                if is_true(m.evaluate(in_city[d][c_idx])):
                    cities_today.append(city)
            assignment.append(cities_today)
        
        # Determine primary city for each day
        primary_city = [None] * days
        primary_city[days-1] = assignment[days-1][0]
        for d in range(days-2, -1, -1):
            cities_today = assignment[d]
            if len(cities_today) == 1:
                primary_city[d] = cities_today[0]
            else:
                if primary_city[d+1] in cities_today:
                    primary_city[d] = primary_city[d+1]
                else:
                    common = set(cities_today) & set(assignment[d+1])
                    if common:
                        primary_city[d] = next(iter(common))
                    else:
                        primary_city[d] = cities_today[0]
        
        # Group consecutive days with the same primary city
        itinerary_list = []
        start_index = 0
        current_city = primary_city[0]
        for d in range(1, days):
            if primary_city[d] != current_city:
                itinerary_list.append({
                    "day_range": f"Day {start_index+1}-{d}",
                    "place": current_city
                })
                start_index = d
                current_city = primary_city[d]
        itinerary_list.append({
            "day_range": f"Day {start_index+1}-{days}",
            "place": current_city
        })
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()