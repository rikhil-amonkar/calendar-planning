from z3 import *

def main():
    s = Solver()
    cities = {
        'Brussels': 0,
        'Helsinki': 1,
        'Split': 2,
        'Dubrovnik': 3,
        'Istanbul': 4,
        'Milan': 5,
        'Vilnius': 6,
        'Frankfurt': 7
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 22

    # Each day is assigned to a city (0-7)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 7)

    # Total days per city: Brussels(3), Helsinki(3), Split(4), Dubrovnik(2), Istanbul(5), Milan(4), Vilnius(5), Frankfurt(3)
    totals = [3, 3, 4, 2, 5, 4, 5, 3]

    for city_code in range(8):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based days)
    # Istanbul days 0-4 (days 1-5 1-based)
    for i in range(5):
        s.add(day_city[i] == cities['Istanbul'])

    # Vilnius days 17-21 (days 18-22 1-based)
    for i in range(17, 22):
        s.add(day_city[i] == cities['Vilnius'])

    # Frankfurt days 15-17 (days 16-18 1-based)
    for i in range(15, 18):
        s.add(day_city[i] == cities['Frankfurt'])

    # Direct flights between consecutive days (including staying in the same city)
    direct_flights = {
        0: [0, 1, 4, 5, 6, 7],    # Brussels
        1: [0, 1, 2, 3, 4, 5, 6, 7], # Helsinki
        2: [1, 2, 5, 6, 7],        # Split
        3: [1, 3, 4, 7],           # Dubrovnik
        4: [0, 1, 4, 5, 6, 7],     # Istanbul
        5: [0, 1, 2, 4, 5, 6, 7],  # Milan
        6: [0, 1, 2, 4, 5, 6, 7],  # Vilnius
        7: [1, 2, 3, 4, 5, 6, 7]   # Frankfurt
    }

    for i in range(days_total - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        allowed = [next_c == n for n in direct_flights.get(current, [current])]
        s.add(Or(allowed))

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