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
        count = Sum([If(Or(x[i] == city, y[i] == city), 1, 0) for i in range(days)])
        s.add(count == total)
    
    s.add(Or(Or(x[6] == 1, y[6] == 1), Or(x[7] == 1, y[7] == 1), Or(x[8] == 1, y[8] == 1)))
    s.add(Or(Or(x[1] == 2, y[1] == 2), Or(x[2] == 2, y[2] == 2)))
    s.add(Or(Or(x[2] == 6, y[2] == 6), Or(x[3] == 6, y[3] == 6), Or(x[4] == 6, y[4] == 6), 
             Or(x[5] == 6, y[5] == 6), Or(x[6] == 6, y[6] == 6)))
    
    s.add(x[1] == 2)
    s.add(y[1] == 6)
    s.add(x[2] == 6)
    s.add(y[2] == 6)
    
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