from z3 import *

def main():
    cities = ['Mykonos', 'Naples', 'Istanbul', 'Venice', 'Dublin', 'Frankfurt', 'Brussels', 'Krakow']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    transport = {
        ('Mykonos', 'Naples'): ['Tuesday', 'Saturday'],
        ('Mykonos', 'Istanbul'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Mykonos', 'Venice'): ['Monday', 'Wednesday', 'Friday'],
        ('Mykonos', 'Krakow'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Naples', 'Mykonos'): ['Tuesday', 'Saturday'],
        ('Naples', 'Istanbul'): ['Monday', 'Wednesday', 'Friday'],
        ('Naples', 'Venice'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Naples', 'Brussels'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Istanbul', 'Mykonos'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Istanbul', 'Naples'): ['Monday', 'Wednesday', 'Friday'],
        ('Istanbul', 'Venice'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Istanbul', 'Dublin'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Istanbul', 'Krakow'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Venice', 'Mykonos'): ['Monday', 'Wednesday', 'Friday'],
        ('Venice', 'Naples'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Venice', 'Istanbul'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Venice', 'Brussels'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Dublin', 'Istanbul'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Dublin', 'Frankfurt'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Dublin', 'Krakow'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Frankfurt', 'Dublin'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Frankfurt', 'Brussels'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Frankfurt', 'Krakow'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Brussels', 'Naples'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Brussels', 'Venice'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Brussels', 'Frankfurt'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Brussels', 'Krakow'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Krakow', 'Mykonos'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Krakow', 'Istanbul'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Krakow', 'Dublin'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Krakow', 'Frankfurt'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'],
        ('Krakow', 'Brussels'): ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']
    }
    
    days_of_week = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']
    
    n_cities = len(cities)
    n_stays = n_cities
    
    s = Solver()
    
    starts = [Int(f'start_{i}') for i in range(n_stays)]
    ends = [Int(f'end_{i}') for i in range(n_stays)]
    city_vars = [Int(f'city_{i}') for i in range(n_stays)]
    
    s.add(city_vars[0] == city_to_idx['Mykonos'])
    s.add(city_vars[n_stays-1] == city_to_idx['Krakow'])
    
    # Minimum stays: 2 days for first/last cities, 1 day for others
    for i in range(n_stays):
        if i == 0 or i == n_stays-1:
            s.add(ends[i] - starts[i] >= 1)  # At least 2 days (inclusive)
        else:
            s.add(ends[i] >= starts[i])  # At least 1 day
    
    s.add(starts[0] == 1)
    s.add(ends[n_stays-1] == 21)
    
    # Maintain sequencing: next stay starts after travel day
    for i in range(n_stays - 1):
        s.add(starts[i+1] == ends[i] + 2)
    
    # Visit each city exactly once
    s.add(Distinct(city_vars))
    
    # Transportation constraints
    for i in range(n_stays - 1):
        travel_day = ends[i] + 1
        day_of_week_index = (travel_day - 1) % 7
        
        from_city = city_vars[i]
        to_city = city_vars[i+1]
        
        valid_days = []
        for (c1, c2), days_list in transport.items():
            if (c1, c2) not in transport:
                continue
            day_indices = [days_of_week.index(d) for d in transport[(c1, c2)]]
            for d_idx in day_indices:
                valid_days.append(And(
                    from_city == city_to_idx[c1],
                    to_city == city_to_idx[c2],
                    day_of_week_index == d_idx
                ))
        s.add(Or(valid_days))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Process first stay
        start0 = m.eval(starts[0]).as_long()
        end0 = m.eval(ends[0]).as_long()
        city0 = cities[m.eval(city_vars[0]).as_long()]
        itinerary.append({'day_range': f'Day {start0}-{end0}', 'place': city0})
        
        # Process intermediate stays and travel
        for i in range(1, n_stays - 1):
            travel_day = end0 + 1
            start_i = m.eval(starts[i]).as_long()
            end_i = m.eval(ends[i]).as_long()
            city_i = cities[m.eval(city_vars[i]).as_long()]
            
            from_city = cities[m.eval(city_vars[i-1]).as_long()]
            to_city = city_i
            itinerary.append({'day_range': f'Day {travel_day}', 'place': f'{from_city}/{to_city}'})
            itinerary.append({'day_range': f'Day {start_i}-{end_i}', 'place': city_i})
            
            end0 = end_i  # Update last end for next travel calculation
        
        # Process final travel and stay
        last_travel = m.eval(ends[n_stays-2]).as_long() + 1
        from_city_last = cities[m.eval(city_vars[n_stays-2]).as_long()]
        to_city_last = cities[m.eval(city_vars[n_stays-1]).as_long()]
        start_last = m.eval(starts[n_stays-1]).as_long()
        end_last = m.eval(ends[n_stays-1]).as_long()
        
        itinerary.append({'day_range': f'Day {last_travel}', 'place': f'{from_city_last}/{to_city_last}'})
        itinerary.append({'day_range': f'Day {start_last}-{end_last}', 'place': to_city_last})
        
        # Format output
        print("{'itinerary': [")
        for idx, item in enumerate(itinerary):
            suffix = "," if idx < len(itinerary)-1 else ""
            print(f"    {{'day_range': '{item['day_range']}', 'place': '{item['place']}'}}{suffix}")
        print("]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()