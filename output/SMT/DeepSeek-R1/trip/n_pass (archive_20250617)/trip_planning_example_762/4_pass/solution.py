from z3 import *

def main():
    s = Solver()
    days = 13
    x = [Int(f'x_{i+1}') for i in range(days)]
    y = [Int(f'y_{i+1}') for i in range(days)]
    
    cities = {
        1: 'Dublin',
        2: 'Madrid',
        3: 'Oslo',
        4: 'London',
        5: 'Vilnius',
        6: 'Berlin'
    }
    
    city_days = {
        1: 3,  # Dublin
        2: 2,  # Madrid
        3: 3,  # Oslo
        4: 2,  # London
        5: 3,  # Vilnius
        6: 5   # Berlin
    }
    
    direct_flights_pairs = [
        (4, 2), (3, 5), (6, 5), (2, 3), (2, 1), (4, 3),
        (2, 6), (6, 3), (1, 3), (4, 1), (4, 6), (6, 1)
    ]
    allowed_flights = set()
    for a, b in direct_flights_pairs:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    allowed_flights_list = list(allowed_flights)
    
    for i in range(days):
        s.add(x[i] >= 1, x[i] <= 6)
        s.add(y[i] >= 1, y[i] <= 6)
    
    for i in range(days - 1):
        s.add(x[i + 1] == y[i])
    
    for i in range(days):
        no_travel = (x[i] == y[i])
        travel_conditions = []
        for a, b in allowed_flights_list:
            travel_conditions.append(And(x[i] == a, y[i] == b))
        s.add(Or(no_travel, Or(travel_conditions)))
    
    for city, total in city_days.items():
        total_count = Sum([If(x[i] == city, 1, 0) for i in range(days)]) + Sum([If(y[i] == city, 1, 0) for i in range(days)])
        s.add(total_count == 2 * total)
    
    dublin_days = [6, 7, 8]  # days 7,8,9 (0-indexed: 6,7,8)
    madrid_days = [1, 2]      # days 2,3 (0-indexed: 1,2)
    berlin_days = [2, 3, 4, 5, 6]  # days 3,4,5,6,7 (0-indexed: 2,3,4,5,6)
    
    s.add(Or([Or(x[i] == 1, y[i] == 1) for i in dublin_days]))
    s.add(Or([Or(x[i] == 2, y[i] == 2) for i in madrid_days]))
    s.add(Or([Or(x[i] == 6, y[i] == 6) for i in berlin_days]))
    
    s.add(x[1] == 2)  # Day 2 starts in Madrid
    s.add(y[1] == 6)  # Day 2 ends in Berlin
    s.add(x[2] == 6)  # Day 3 starts in Berlin
    s.add(y[2] == 6)  # Day 3 ends in Berlin (stay in Berlin)
    
    if s.check() == sat:
        model = s.model()
        x_vals = [model.evaluate(x[i]).as_long() for i in range(days)]
        y_vals = [model.evaluate(y[i]).as_long() for i in range(days)]
        
        for d in range(days):
            day = d + 1
            x_city = cities[x_vals[d]]
            y_city = cities[y_vals[d]]
            if x_vals[d] == y_vals[d]:
                print(f"Day {day}: Stay in {x_city}")
            else:
                print(f"Day {day}: Travel from {x_city} to {y_city}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()