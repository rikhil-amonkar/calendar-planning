from z3 import *

def main():
    s = Solver()
    cities = {
        'Mykonos': 0,
        'Riga': 1,
        'Munich': 2,
        'Bucharest': 3,
        'Rome': 4,
        'Nice': 5,
        'Krakow': 6
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 17

    # Assign each day to a city (0-6)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 6)

    # Total days per city constraints
    totals = [3, 3, 4, 4, 4, 3, 2]
    for city_code in range(7):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based)
    # Rome days 0-3 (1-based 1-4)
    for i in range(4):
        s.add(day_city[i] == cities['Rome'])
    # Mykonos days 3-5 (1-based 4-6)
    for i in [3, 4, 5]:
        s.add(day_city[i] == cities['Mykonos'])
    # Krakow days 15-16 (1-based 16-17)
    s.add(day_city[15] == cities['Krakow'])
    s.add(day_city[16] == cities['Krakow'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 2, 5, 4],       # Mykonos
        1: [1, 5, 3, 2],       # Riga
        2: [2, 3, 0, 4, 5, 6], # Munich
        3: [3, 2, 1, 4],       # Bucharest
        4: [4, 5, 2, 0, 3, 1], # Rome
        5: [5, 1, 4, 2, 0],    # Nice
        6: [6, 2]              # Krakow
    }

    # Ensure consecutive days are connected by direct flights
    for i in range(days_total - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        allowed = direct_flights.get(current, [current])
        s.add(Or([next_day == a for a in allowed]))

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