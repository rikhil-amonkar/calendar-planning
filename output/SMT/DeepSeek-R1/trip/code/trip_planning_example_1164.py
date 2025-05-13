from z3 import *

def main():
    s = Solver()
    cities = {
        'Reykjavik': 0,
        'Stockholm': 1,
        'Porto': 2,
        'Nice': 3,
        'Venice': 4,
        'Vienna': 5,
        'Split': 6,
        'Copenhagen': 7
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 17

    # Each day is assigned to a city (0-7)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 7)

    # Total days per city
    totals = [2, 2, 5, 3, 4, 3, 3, 2]

    for city_code in range(8):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based)
    # Reykjavik days 2-3 (days 3-4 1-based)
    s.add(day_city[2] == cities['Reykjavik'])
    s.add(day_city[3] == cities['Reykjavik'])

    # Stockholm days 3-4 (days 4-5 1-based)
    s.add(day_city[3] == cities['Stockholm'])
    s.add(day_city[4] == cities['Stockholm'])

    # Vienna days 10-12 (days 11-13 1-based)
    for i in range(10, 13):
        s.add(day_city[i] == cities['Vienna'])

    # Porto days 12-16 (days 13-17 1-based)
    for i in range(12, 17):
        s.add(day_city[i] == cities['Porto'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 3, 5, 7, 1],       # Reykjavik
        1: [1, 3, 7, 5, 0, 6],    # Stockholm
        2: [2, 3, 7, 5],          # Porto
        3: [3, 1, 0, 2, 4, 5, 7], # Nice
        4: [4, 3, 5, 7],          # Venice
        5: [5, 7, 0, 3, 1, 4, 6, 2], # Vienna
        6: [6, 7, 5, 1],          # Split
        7: [7, 5, 6, 1, 0, 3, 4, 2]  # Copenhagen
    }

    # Flight constraints between consecutive days
    for i in range(days_total - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        for city_code in range(8):
            allowed = direct_flights[city_code]
            s.add(Implies(current == city_code, Or([next_day == nc for nc in allowed])))

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