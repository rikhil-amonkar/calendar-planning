from z3 import *

def main():
    cities = ['Oslo', 'Dubrovnik', 'Helsinki', 'Krakow', 'Vilnius', 'Paris', 'Madrid', 'Mykonos']
    req_days = {
        'Oslo': 2,
        'Dubrovnik': 3,
        'Helsinki': 2,
        'Krakow': 5,
        'Vilnius': 2,
        'Paris': 2,
        'Madrid': 5,
        'Mykonos': 4
    }
    flights = { 
        ('Oslo', 'Krakow'), ('Oslo', 'Paris'), ('Paris', 'Madrid'), ('Helsinki', 'Vilnius'), 
        ('Oslo', 'Madrid'), ('Oslo', 'Helsinki'), ('Helsinki', 'Krakow'), ('Dubrovnik', 'Helsinki'),
        ('Dubrovnik', 'Madrid'), ('Oslo', 'Dubrovnik'), ('Krakow', 'Paris'), ('Madrid', 'Mykonos'),
        ('Oslo', 'Vilnius'), ('Krakow', 'Vilnius'), ('Helsinki', 'Paris'), ('Vilnius', 'Paris'),
        ('Helsinki', 'Madrid')
    }
    sequence = ['Oslo', 'Dubrovnik', 'Helsinki', 'Krakow', 'Vilnius', 'Paris', 'Madrid', 'Mykonos']

    start = {city: Int(f'start_{city}') for city in cities}
    end = {city: Int(f'end_{city}') for city in cities}

    s = Solver()

    s.add(start['Oslo'] == 1)
    s.add(end['Oslo'] == 2)
    s.add(start['Dubrovnik'] == 3)
    s.add(end['Dubrovnik'] == 5)
    s.add(start['Mykonos'] == 15)
    s.add(end['Mykonos'] == 18)

    for i in range(len(sequence) - 1):
        city1 = sequence[i]
        city2 = sequence[i+1]
        s.add(end[city1] + 1 == start[city2])
        s.add(Or((city1, city2) in flights, (city2, city1) in flights))

    for city in cities:
        s.add(end[city] - start[city] + 1 == req_days[city])
        s.add(start[city] >= 1, end[city] <= 18)

    if s.check() == sat:
        m = s.model()
        result = [None] * 18
        for city in sequence:
            start_val = m.eval(start[city]).as_long()
            end_val = m.eval(end[city]).as_long()
            for d in range(start_val, end_val + 1):
                if d <= 18:
                    result[d-1] = city
        
        itinerary_list = []
        current_city = result[0]
        start_day = 1
        for idx in range(1, 18):
            if result[idx] == current_city:
                continue
            else:
                end_day = idx
                itinerary_list.append({'day_range': f'Day {start_day}-{end_day}', 'place': current_city})
                current_city = result[idx]
                start_day = idx + 1
        itinerary_list.append({'day_range': f'Day {start_day}-18', 'place': current_city})
        print('Plan found:', {"itinerary": itinerary_list})
    else:
        print("Unsatisfiable")

if __name__ == "__main__":
    main()