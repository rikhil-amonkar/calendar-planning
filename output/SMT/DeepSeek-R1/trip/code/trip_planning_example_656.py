from z3 import *

def main():
    s = Solver()
    cities = {
        'Reykjavik': 0,
        'Istanbul': 1,
        'Edinburgh': 2,
        'Oslo': 3,
        'Stuttgart': 4,
        'Bucharest': 5
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 19

    # Assign each day to a city (0-5)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 5)

    # Total days per city constraints
    totals = [5, 4, 5, 2, 3, 5]
    for city_code in range(6):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based)
    # Istanbul days 4-7 (1-based 5-8)
    for i in [4, 5, 6, 7]:
        s.add(day_city[i] == cities['Istanbul'])
    # Oslo days 7-8 (1-based 8-9)
    s.add(day_city[7] == cities['Oslo'])
    s.add(day_city[8] == cities['Oslo'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 3, 4],        # Reykjavik
        1: [1, 3, 5, 2, 4],  # Istanbul
        2: [2, 4, 1, 3],     # Edinburgh
        3: [3, 5, 1, 0, 2],  # Oslo
        4: [4, 2, 1],        # Stuttgart
        5: [5, 3, 1]         # Bucharest
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