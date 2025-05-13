from z3 import *

def main():
    s = Solver()
    cities = {
        'Mykonos': 0,
        'Krakow': 1,
        'Vilnius': 2,
        'Helsinki': 3,
        'Dubrovnik': 4,
        'Oslo': 5,
        'Madrid': 6,
        'Paris': 7
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 18

    # Each day is assigned to a city (0-7)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 7)

    # Total days per city constraints
    totals = [4, 5, 2, 2, 3, 2, 5, 2]
    for city_code in range(8):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based)
    # Oslo days 0 and 1 (1-based days 1-2)
    s.add(day_city[0] == cities['Oslo'])
    s.add(day_city[1] == cities['Oslo'])
    # Dubrovnik days 1-3 (1-based days 2-4)
    s.add(day_city[1] == cities['Dubrovnik'])
    s.add(day_city[2] == cities['Dubrovnik'])
    s.add(day_city[3] == cities['Dubrovnik'])
    # Mykonos days 14-17 (1-based days 15-18)
    for i in range(14, 18):
        s.add(day_city[i] == cities['Mykonos'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [6],                   # Mykonos only connects to Madrid
        1: [5, 7, 3, 2],          # Krakow: Oslo, Paris, Helsinki, Vilnius
        2: [3, 5, 1, 7],          # Vilnius: Helsinki, Oslo, Krakow, Paris
        3: [2, 5, 1, 4, 7, 6],    # Helsinki: Vilnius, Oslo, Krakow, Dubrovnik, Paris, Madrid
        4: [3, 6, 5],             # Dubrovnik: Helsinki, Madrid, Oslo
        5: [1, 7, 6, 3, 4, 2],   # Oslo: Krakow, Paris, Madrid, Helsinki, Dubrovnik, Vilnius
        6: [7, 5, 4, 0, 3],      # Madrid: Paris, Oslo, Dubrovnik, Mykonos, Helsinki
        7: [5, 6, 1, 3, 2]       # Paris: Oslo, Madrid, Krakow, Helsinki, Vilnius
    }

    # Ensure consecutive days are connected by direct flights or same city
    for i in range(days_total - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        allowed = direct_flights.get(current, [current])
        s.add(Or([next_c == nc for nc in allowed]))

    if s.check() == sat:
        model = s.model()
        schedule = [model.evaluate(day).as_long() for day in day_city]
        print("Day  City")
        for idx, city_code in enumerate(schedule):
            print(f"{idx + 1:3}  {city_names[city_code]}")
    else:
        print("No valid trip plan exists.")

if __name__ == "__main__":
    main()