from z3 import *

def main():
    cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
    city2idx = {city: idx for idx, city in enumerate(cities)}
    
    given_edges = [
        ('Krakow', 'Split'), ('Split', 'Athens'), ('Edinburgh', 'Krakow'), ('Venice', 'Stuttgart'),
        ('Krakow', 'Stuttgart'), ('Edinburgh', 'Stuttgart'), ('Stuttgart', 'Athens'), ('Venice', 'Edinburgh'),
        ('Athens', 'Mykonos'), ('Venice', 'Athens'), ('Stuttgart', 'Split'), ('Edinburgh', 'Athens')
    ]
    
    flight_edges = []
    for u, v in given_edges:
        u_idx = city2idx[u]
        v_idx = city2idx[v]
        flight_edges.append((u_idx, v_idx))
        flight_edges.append((v_idx, u_idx))
    
    # Array of 21 variables for days 0-20
    x = [Int('x%d' % i) for i in range(21)]
    s = Solver()
    
    # Each variable must be between 0 and 6 (city indices)
    for i in range(21):
        s.add(And(x[i] >= 0, x[i] < 7))
    
    # Start and stay in Venice for first 5 days (x0 to x5 inclusive)
    for i in range(6):
        s.add(x[i] == city2idx['Venice'])
    
    # Flight constraints between different cities
    for i in range(20):
        s.add(Implies(
            x[i] != x[i+1],
            Or([And(x[i] == a, x[i+1] == b) for (a, b) in flight_edges])
        ))
    
    # Calculate total time per city (including partial days)
    totals = [0] * 7
    for a in range(7):
        total_expr = 0
        for i in range(1, 21):
            # Count partial days: 0.5 for morning, 0.5 for evening
            cond1 = If(x[i-1] == a, 0.5, 0)
            cond2 = If(x[i] == a, 0.5, 0)
            total_expr += (cond1 + cond2)
        totals[a] = total_expr
    
    # Add city duration constraints
    s.add(totals[city2idx['Stuttgart']] == 3.0)
    s.add(totals[city2idx['Edinburgh']] == 4.0)
    s.add(totals[city2idx['Athens']] == 4.0)
    s.add(totals[city2idx['Split']] == 2.0)
    s.add(totals[city2idx['Krakow']] == 4.0)
    s.add(totals[city2idx['Venice']] == 5.0)
    s.add(totals[city2idx['Mykonos']] == 4.0)
    
    # Time window constraints
    def in_city(day, city_idx):
        return Or(x[day-1] == city_idx, x[day] == city_idx)
    
    # Fixed syntax for multi-line Or constraints
    s.add(Or(
        in_city(11, city2idx['Stuttgart']),
        in_city(12, city2idx['Stuttgart']),
        in_city(13, city2idx['Stuttgart'])
    ))
    
    s.add(Or(
        in_city(13, city2idx['Split']),
        in_city(14, city2idx['Split'])
    ))
    
    s.add(Or(
        in_city(8, city2idx['Krakow']),
        in_city(9, city2idx['Krakow']),
        in_city(10, city2idx['Krakow']),
        in_city(11, city2idx['Krakow'])
    ))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = cities[model[x[0]].as_long()]
        start_day = 1
        # Group consecutive days in the same city
        for day in range(1, 21):
            place = cities[model[x[day]].as_long()]
            if place != current_place:
                end_day = day
                itinerary.append({
                    'day_range': f'Day {start_day}-{end_day}',
                    'place': current_place
                })
                current_place = place
                start_day = day + 1
        # Add the last segment
        itinerary.append({
            'day_range': f'Day {start_day}-20',
            'place': current_place
        })
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()